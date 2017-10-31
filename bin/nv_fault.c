#include <stdlib.h>
#include <limits.h>
#include <unistd.h>
#include <sys/mman.h>

#include <nvif/client.h>
#include <nvif/driver.h>
#include <nvif/device.h>
#include <nvif/mem.h>
#include <nvif/notify.h>
#include <nvif/vmm.h>

#include <nvif/class.h>
#include <nvif/cla06f.h>
#include <nvif/clb069.h>

#include "util.h"

static struct nvif_device device;
static struct nvif_mmu mmu;
static struct nvif_vmm vmm;

struct vram {
	struct nvif_mem mem;
	struct nvif_vma vma;
};

static void
vram_put(struct nvif_device *device, struct vram *vram)
{
	nvif_vmm_put(&vmm, &vram->vma);
	nvif_mem_fini(&vram->mem);
}

static void
vram_get_(struct nvif_device *device, u64 size, struct vram *vram, bool map)
{
	int ret;

	ret = nvif_mem_init(&mmu, NVIF_CLASS_MEM_GF100, NVIF_MEM_VRAM |
			    NVIF_MEM_MAPPABLE, 0, size, NULL, 0,
			    &vram->mem);
	assert(ret == 0);

	if (map) {
		ret = nvif_vmm_get(&vmm, ADDR, false, 0, 0, vram->mem.size,
				   &vram->vma);
		assert(ret == 0);
		ret = nvif_vmm_map(&vmm, vram->vma.addr, vram->mem.size,
				   NULL, 0, &vram->mem, 0);
		assert(ret == 0);
	} else {
		vram->vma.size = 0;
	}

	ret = nvif_object_map(&vram->mem.object, NULL, 0);
	assert(ret == 0);
}

static void
vram_get(struct nvif_device *device, u64 size, struct vram *vram)
{
	vram_get_(device, size, vram, true);
}

static bool chan_dead = false;
static int
chan_killed(struct nvif_notify *notify)
{
	printk(KERN_ERR "CHANNEL KILLED\n");
	chan_dead = true;
	return NVIF_NOTIFY_DROP;
}

static struct nvif_object rpfb;
static struct vram *rpfb_vram = NULL;
static int
rpfb_process(struct nvif_notify *notify)
{
	u32 get = nvif_rd32(&device.object, 0x002a7c);
	u32 put = nvif_rd32(&device.object, 0x002a80);
	if (put != get) {
		printk(KERN_ERR "RPFB GET %08x PUT %08x\n", get, put);
		for (; get != put; get++) {
			const u32 instlo = nvif_rd32(&rpfb, (get * 32) + 0x00);
			const u32 insthi = nvif_rd32(&rpfb, (get * 32) + 0x04);
			const u32 addrlo = nvif_rd32(&rpfb, (get * 32) + 0x08);
			const u32 addrhi = nvif_rd32(&rpfb, (get * 32) + 0x0c);
			const u32 timelo = nvif_rd32(&rpfb, (get * 32) + 0x10);
			const u32 timehi = nvif_rd32(&rpfb, (get * 32) + 0x14);
			const u32   rsvd = nvif_rd32(&rpfb, (get * 32) + 0x18);
			const u32   info = nvif_rd32(&rpfb, (get * 32) + 0x1c);
			const u32  valid = (info & 0x80000000) >> 31;
			const u32    gpc = (info & 0x1f000000) >> 24;
			const u32  isgpc = (info & 0x00100000) >> 20;
			const u32 access = (info & 0x00070000) >> 16;
			const u32 client = (info & 0x00007f00) >> 8;
			const u32  fault = (info & 0x0000001f) >> 0;
			int ret;

			printk(KERN_ERR "%08x: \t%08x\n", get, instlo);
			printk(KERN_ERR "\t\t%08x\n", insthi);
			printk(KERN_ERR "\t\t%08x\n", addrlo);
			printk(KERN_ERR "\t\t%08x\n", addrhi);
			printk(KERN_ERR "\t\t%08x\n", timelo);
			printk(KERN_ERR "\t\t%08x\n", timehi);
			printk(KERN_ERR "\t\t%08x\n",   rsvd);
			printk(KERN_ERR "\t\t%08x\n",   info);
			(void)fault; (void)access;

			nvif_wr32(&device.object, 0x002a7c, get + 1);
			if (!valid)
				continue;

			nvif_mask(&rpfb, 0x1c, 0x80000000, 0x00000000);

			if (!rpfb_vram) {
				nvif_wr32(&device.object, 0x100cbc, 0x80000000 |
					  (4 << 3) | (client << 9) |
					  (gpc << 15) | (isgpc << 20));
				continue;
			}

			ret = nvif_vmm_map(&vmm, (u64)addrhi << 32 | addrlo,
					   rpfb_vram->mem.size, NULL, 0,
					   &rpfb_vram->mem, 0);
			assert(ret == 0);

			nvif_wr32(&device.object, 0x100cbc, 0x80000000 |
				  (1 << 3) | (client << 9) |
				  (gpc << 15) | (isgpc << 20));
		}
	}
	return NVIF_NOTIFY_KEEP;
}

struct nvif_object chan;
static u32 push_pbput = 0;
static u32 push_pbcur = 0;
static struct vram push;

static void
DATA(u32 data) {
	printk(KERN_ERR "%08x: %08x\n", push_pbcur * 4, data);
	((u32 *)push.mem.object.map.ptr)[push_pbcur++] = data;
}

static void
INCR(int s, u32 m, int n)
{
	DATA(0x20000000 | ((n) << 16) | ((s) << 13) | ((m) >> 2));
}

static void
NINC(int s, u32 m, int n)
{
	DATA(0x60000000 | ((n) << 16) | ((s) << 13) | ((m) >> 2));
}

static void
IMMD(int s, u32 m, u16 d)
{
	DATA(0x80000000 | ((d) << 16) | ((s) << 13) | ((m) >> 2));
}

static void
KICK(void)
{
	u64 addr = push.vma.addr + (push_pbput * 4);
	u32 put = nvif_rd32(&chan, 0x8c);
	u32 *ib = (u32 *)((u8 *)push.mem.object.map.ptr + 0x10000 + (put * 8));
	ib[0] = lower_32_bits(addr);
	ib[1] = upper_32_bits(addr) | ((push_pbcur - push_pbput) << 10);
	nvif_wr32(&chan, 0x8c, ++put);
	push_pbput = push_pbcur;
	printk(KERN_ERR "KICK %08x%08x (%d)\n", ib[1], ib[0], put);
}

static void
IDLE(void)
{
	u32 refcnt = rand();
	INCR(0, 0x50, 1);
	DATA(refcnt);
	KICK();
	if (nvif_msec(&device, 2000,
		if (nvif_rd32(&chan, 0x48) == refcnt)
			break;
	) < 0)
		assert(0);
}

struct gp100_cp_launch_desc
{
   u32 unk0[8];
   u32 entry;
   u32 unk9[2];
   u32 unk11_0      : 30;
   u32 linked_tsc   : 1;
   u32 unk11_31     : 1;
   u32 griddim_x    : 31;
   u32 unk12        : 1;
   u16 griddim_y;
   u16 unk13;
   u16 griddim_z;
   u16 unk14;
   u32 unk15[2];
   u32 shared_size  : 18;
   u32 unk17        : 14;
   u16 unk18;
   u16 blockdim_x;
   u16 blockdim_y;
   u16 blockdim_z;
   u32 cb_mask      : 8;
   u32 unk20        : 24;
   u32 unk21[8];
   u32 local_size_p : 24;
   u32 unk29        : 3;
   u32 bar_alloc    : 5;
   u32 local_size_n : 24;
   u32 gpr_alloc    : 8;
   u32 cstack_size  : 24;
   u32 unk31        : 8;
   struct {
      u32 address_l;
      u32 address_h : 17;
      u32 reserved  : 2;
      u32 size_sh4  : 13;
   } cb[8];
   u32 unk48[16];
};

static struct vram desc;
static struct vram parm;
static void
test(u64 addr, bool valid)
{
	struct gp100_cp_launch_desc *d = desc.mem.object.map.ptr;
	u32 value;

	srand(time(NULL));
	value = rand();

	memset(d, 0x00, sizeof(*d));
	d->unk0[4]  = 0x40;
	d->unk11_0  = 0x04014000;
	d->entry = 0;
	d->griddim_x = 1;
	d->griddim_y = 1;
	d->griddim_z = 1;
	d->blockdim_x = 1;
	d->blockdim_y = 1;
	d->blockdim_z = 1;
	d->shared_size = 0;
	d->local_size_p = 0;
	d->local_size_n = 0;
	d->cstack_size = 0x800;
	d->gpr_alloc = 3;
	d->bar_alloc = 0;
	d->cb[0].address_l = parm.vma.addr;
	d->cb[0].address_h = parm.vma.addr >> 32;
	d->cb[0].size_sh4 = DIV_ROUND_UP(parm.mem.size, 16);
	d->cb_mask = 1;

	INCR(1, 0x0180, 4);
	DATA(12);
	DATA(1);
	DATA(upper_32_bits(parm.vma.addr));
	DATA(lower_32_bits(parm.vma.addr));
	INCR(1, 0x01b0, 1);
	DATA(0x00000041);
	NINC(1, 0x01b4, 3);
	DATA(upper_32_bits(addr));
	DATA(lower_32_bits(addr));
	DATA(value);
	INCR(1, 0x1698, 1);
	DATA(0x00001000);
	INCR(1, 0x021c, 1);
	DATA(0x00001017);
	INCR(1, 0x0274, 3);
	DATA(upper_32_bits(parm.vma.addr));
	DATA(lower_32_bits(parm.vma.addr));
	DATA(0x80000010);

	INCR(1, 0x02b4, 1);
	DATA(desc.vma.addr >> 8);
	INCR(1, 0x02bc, 1);
	DATA(0x00000003);
	INCR(1, 0x0110, 1);
	DATA(0x00000000);
	KICK();

	/* expected channel death due to unrecoverable page fault */
	if (!rpfb_vram) {
		if (nvif_msec(&device, 2000,
			if (chan_dead)
				break;
		) < 0) {
			assert(0);
		};
		/* recovery race war */
		sleep(2);
		return;
	}

	IDLE();
	if (((u32 *)rpfb_vram->mem.object.map.ptr)[0] != value) {
		fprintf(stderr, "FAIL!!!\n");
//		assert(0);
	}
}

static u32 kernel[] = {
	0xfc0007e0,
	0x001f8000,
	0x00170000,
	0x4c980780,
	0x00070001,
	0x4c980780,
	0x00270002,
	0x4c980780,
	0xfc0007e0,
	0x001f8000,
	0x00070002,
	0xbf900000,
	0x0007000f,
	0xe3000000,
	0x0007000f,
	0xe3000000,
};

int
main(int argc, char **argv)
{
	static const struct nvif_mclass mmus[] = {
		{ NVIF_CLASS_MMU_GF100, -1 },
		{}
	};
	static const struct nvif_mclass vmms[] = {
		{ NVIF_CLASS_VMM_GP100, -1 },
		{}
	};
	static const struct nvif_mclass rpfbs[] = {
		{ MAXWELL_FAULT_BUFFER_A, -1 },
		{}
	};
	static const struct nvif_mclass fifos[] = {
		{ PASCAL_CHANNEL_GPFIFO_A, 0 },
		{}
	};
	static const struct nvif_mclass computes[] = {
		{ PASCAL_COMPUTE_B, -1 },
		{ PASCAL_COMPUTE_A, -1 },
		{}
	};
	struct nvif_client client;
	int ret, c;

	while ((c = getopt(argc, argv, U_GETOPT)) != -1) {
		switch (c) {
		default:
			if (!u_option(c))
				return 1;
			break;
		}
	}

	ret = u_device(NULL, argv[0], "info", true, true, ~0ULL,
		       0x00000000, &client, &device);
	if (ret)
		return ret;

	/* Allocate MMU. */
	ret = nvif_mclass(&device.object, mmus);
	assert(ret >= 0);
	ret = nvif_mmu_init(&device.object, mmus[ret].oclass, &mmu);
	assert(ret == 0);

	/* Allocate VMM. */
	ret = nvif_mclass(&mmu.object, vmms);
	assert(ret >= 0);
	ret = nvif_vmm_init(&mmu, vmms[ret].oclass, 0, 0, NULL, 0, &vmm);
	assert(ret == 0);

	/* Reserve a chunk of (low) address-space for channel buffers. */
	const u64 reserved_size = 128 * 1024 * 1024;
	void *reserved = mmap(NULL, reserved_size, PROT_NONE, MAP_PRIVATE |
			      MAP_32BIT | MAP_ANONYMOUS, -1, 0);
	const u64 reserved_addr = (unsigned long)reserved;
	assert(reserved_addr);

	/* ... The space before the reserved chunk. */
	struct nvif_vma reserved_vma[3];
	ret = nvif_vmm_get(&vmm, ADDR, false, 0, 0, reserved_addr,
			   &reserved_vma[0]);
	assert(ret == 0 && reserved_vma[0].addr == 0ULL);

	/* ... The reserved chunk. */
	ret = nvif_vmm_get(&vmm, ADDR, false, 0, 0, reserved_size,
			   &reserved_vma[1]);
	assert(ret == 0 && reserved_vma[1].addr == reserved_addr);

	/* ... The space after the reserved chunk. */
	ret = nvif_vmm_get(&vmm, ADDR, false, 0, 0,
			   vmm.limit - (reserved_addr + reserved_size),
			   &reserved_vma[2]);
	assert(ret == 0 &&
	       reserved_vma[2].addr == reserved_addr + reserved_size);

	/* Allow the reserved chunk to be allocated normally again. */
	nvif_vmm_put(&vmm, &reserved_vma[1]);

	/* Allocate replayable fault buffer. */
	ret = nvif_mclass(&device.object, rpfbs);
	assert(ret >= 0);
	ret = nvif_object_init(&device.object, 0, rpfbs[ret].oclass,
			       NULL, 0, &rpfb);
	assert(ret == 0);
	nvif_object_map(&rpfb, NULL, 0);

	/* Request notification of pending replayable faults. */
	struct nvif_notify pending;
	ret = nvif_notify_init(&rpfb, rpfb_process, true, NVB069_VN_NTFY_FAULT,
			       NULL, 0, 0, &pending);
	assert(ret == 0);
	ret = nvif_notify_get(&pending);
	assert(ret == 0);

	/* Allocate push buffer. */
	vram_get(&device, 0x11000, &push);

	/* Allocate channel. */
	ret = nvif_mclass(&device.object, fifos);
	assert(ret >= 0);
	ret = nvif_object_init(&device.object, 0, fifos[ret].oclass,
			       &(struct kepler_channel_gpfifo_a_v0) {
				.engines = NVA06F_V0_ENGINE_GR,
				.ilength = 0x1000,
				.ioffset = push.vma.addr + 0x10000,
				.vmm = nvif_handle(&vmm.object),
			       }, sizeof(struct kepler_channel_gpfifo_a_v0),
			       &chan);
	assert(ret == 0);
	nvif_object_map(&chan, NULL, 0);

	/* Request notification of channel death (for non-replayable fault). */
	struct nvif_notify killed;
	ret = nvif_notify_init(&chan, chan_killed, true, NVA06F_V0_NTFY_KILLED,
			       NULL, 0, 0, &killed);
	assert(ret == 0);
	ret = nvif_notify_get(&killed);
	assert(ret == 0);

	/* Test channel is working. */
	IDLE();
	IDLE();

	/* Allocate compute, and test subchannel bind. */
	struct nvif_object compute;
	ret = nvif_mclass(&chan, computes);
	assert(ret >= 0);
	ret = nvif_object_init(&chan, 0, computes[ret].oclass,
			       NULL, 0, &compute);
	assert(ret == 0);

	INCR(1, 0x0000, 1);
	DATA(compute.oclass);
	KICK();
	IDLE();

	/* Setup compute resources. */
	const int mp_count = 16;
	struct vram code;
	struct vram heap;
	struct vram temp;
	vram_get(&device,  1 << 20, &code);
	vram_get(&device,  1 << 16, &desc);
	vram_get_(&device, 1 << 20, &heap, false);
	vram_get(&device,  1 << 16, &parm);
	vram_get(&device, 16 << 20, &temp);

	INCR(1, 0x0790, 2);
	DATA(upper_32_bits(temp.vma.addr));
	DATA(lower_32_bits(temp.vma.addr));
	INCR(1, 0x02e4, 3);
	DATA(upper_32_bits(temp.mem.size / mp_count));
	DATA(lower_32_bits(temp.mem.size / mp_count) & ~0x7fff);
	DATA(0x000000ff);
	INCR(1, 0x02f0, 3);
	DATA(upper_32_bits(temp.mem.size / mp_count));
	DATA(lower_32_bits(temp.mem.size / mp_count) & ~0x7fff);
	DATA(0x000000ff);
	INCR(1, 0x077c, 1);
	DATA(0xff000000);
	INCR(1, 0x0214, 1);
	DATA(0xfe000000);
	INCR(1, 0x1608, 2);
	DATA(upper_32_bits(code.vma.addr));
	DATA(lower_32_bits(code.vma.addr));
	INCR(1, 0x0310, 1);
	DATA(0x00000400);
	NINC(1, 0x0248, 64);
	for (int i = 63; i >= 0; --i)
		DATA(0x00038000 | i);
	IMMD(1, 0x0110, 0x0000);
	INCR(1, 0x2608, 1);
	DATA(0);
	INCR(1, 0x0180, 4);
	DATA(sizeof(kernel));
	DATA(1);
	DATA(upper_32_bits(code.vma.addr));
	DATA(lower_32_bits(code.vma.addr));
	INCR(1, 0x01b0, 1);
	DATA(0x00000041);
	NINC(1, 0x01b4, sizeof(kernel) / 4);
	for (int i = 0; i < sizeof(kernel) / 4; ++i)
		DATA(kernel[i]);
	KICK();
	IDLE();

	/* Test replayable fault (valid address). */
	u32 *buffer = malloc(heap.mem.size + 0x1000);
	u64 buffer_addr = ((unsigned long)(void *)buffer + 0xfff) & ~0xfff;
	assert(buffer);
	printk(KERN_ERR "buffer @ %016llx\n", buffer_addr);
	rpfb_vram = &heap;
	test(buffer_addr, true);

	/* Test replayable fault (invalid address). */
	rpfb_vram = NULL;
	test(0xabcd0000, false);

	/* Cleanup! */
	printf("shutting down...\n");
	vram_put(&device, &temp);
	vram_put(&device, &parm);
	vram_put(&device, &heap);
	vram_put(&device, &desc);
	vram_put(&device, &code);
	nvif_object_fini(&compute);
	nvif_notify_fini(&killed);
	nvif_object_fini(&chan);
	vram_put(&device, &push);
	nvif_notify_fini(&pending);
	nvif_object_fini(&rpfb);
	nvif_vmm_fini(&vmm);
	munmap(reserved, reserved_size);
	nvif_mmu_fini(&mmu);
	nvif_device_fini(&device);
	nvif_client_fini(&client);
	printf("done!\n");
	return ret;
}
