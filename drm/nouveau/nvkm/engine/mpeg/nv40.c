/*
 * Copyright 2012 Red Hat Inc.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE COPYRIGHT HOLDER(S) OR AUTHOR(S) BE LIABLE FOR ANY CLAIM, DAMAGES OR
 * OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
 * ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 *
 * Authors: Ben Skeggs
 */
#include "nv31.h"

#include <subdev/instmem.h>

/*******************************************************************************
 * MPEG object classes
 ******************************************************************************/

static int
nv40_mpeg_mthd_dma(struct nvkm_object *object, u32 mthd, void *arg, u32 len)
{
	struct nv31_mpeg *mpeg = (void *)object->engine;
	struct nvkm_device *device = mpeg->base.engine.subdev.device;
	struct nvkm_instmem *imem = device->imem;
	u32 inst = *(u32 *)arg << 4;
	u32 dma0 = nv_ro32(imem, inst + 0);
	u32 dma1 = nv_ro32(imem, inst + 4);
	u32 dma2 = nv_ro32(imem, inst + 8);
	u32 base = (dma2 & 0xfffff000) | (dma0 >> 20);
	u32 size = dma1 + 1;

	/* only allow linear DMA objects */
	if (!(dma0 & 0x00002000))
		return -EINVAL;

	if (mthd == 0x0190) {
		/* DMA_CMD */
		nvkm_mask(device, 0x00b300, 0x00030000, (dma0 & 0x00030000));
		nvkm_wr32(device, 0x00b334, base);
		nvkm_wr32(device, 0x00b324, size);
	} else
	if (mthd == 0x01a0) {
		/* DMA_DATA */
		nvkm_mask(device, 0x00b300, 0x000c0000, (dma0 & 0x00030000) << 2);
		nvkm_wr32(device, 0x00b360, base);
		nvkm_wr32(device, 0x00b364, size);
	} else {
		/* DMA_IMAGE, VRAM only */
		if (dma0 & 0x00030000)
			return -EINVAL;

		nvkm_wr32(device, 0x00b370, base);
		nvkm_wr32(device, 0x00b374, size);
	}

	return 0;
}

static struct nvkm_omthds
nv40_mpeg_omthds[] = {
	{ 0x0190, 0x0190, nv40_mpeg_mthd_dma },
	{ 0x01a0, 0x01a0, nv40_mpeg_mthd_dma },
	{ 0x01b0, 0x01b0, nv40_mpeg_mthd_dma },
	{}
};

struct nvkm_oclass
nv40_mpeg_sclass[] = {
	{ 0x3174, &nv31_mpeg_ofuncs, nv40_mpeg_omthds },
	{}
};

/*******************************************************************************
 * PMPEG engine/subdev functions
 ******************************************************************************/

static void
nv40_mpeg_intr(struct nvkm_subdev *subdev)
{
	struct nv31_mpeg *mpeg = (void *)subdev;
	struct nvkm_device *device = mpeg->base.engine.subdev.device;
	u32 stat;

	if ((stat = nvkm_rd32(device, 0x00b100)))
		nv31_mpeg_intr(subdev);

	if ((stat = nvkm_rd32(device, 0x00b800))) {
		nvkm_error(subdev, "PMSRCH %08x\n", stat);
		nvkm_wr32(device, 0x00b800, stat);
	}
}

static int
nv40_mpeg_ctor(struct nvkm_object *parent, struct nvkm_object *engine,
	       struct nvkm_oclass *oclass, void *data, u32 size,
	       struct nvkm_object **pobject)
{
	struct nv31_mpeg *mpeg;
	int ret;

	ret = nvkm_mpeg_create(parent, engine, oclass, &mpeg);
	*pobject = nv_object(mpeg);
	if (ret)
		return ret;

	nv_subdev(mpeg)->unit = 0x00000002;
	nv_subdev(mpeg)->intr = nv40_mpeg_intr;
	nv_engine(mpeg)->cclass = &nv31_mpeg_cclass;
	nv_engine(mpeg)->sclass = nv40_mpeg_sclass;
	nv_engine(mpeg)->tile_prog = nv31_mpeg_tile_prog;
	return 0;
}

struct nvkm_oclass
nv40_mpeg_oclass = {
	.handle = NV_ENGINE(MPEG, 0x40),
	.ofuncs = &(struct nvkm_ofuncs) {
		.ctor = nv40_mpeg_ctor,
		.dtor = _nvkm_mpeg_dtor,
		.init = nv31_mpeg_init,
		.fini = _nvkm_mpeg_fini,
	},
};
