#ifndef __NVKM_OS_H__
#define __NVKM_OS_H__
#include <nvif/os.h>

#define nouveau_client nvkm_client
#define nouveau_client_name nvkm_client_name
#define nouveau_client_create nvkm_client_create
#define nouveau_client_init nvkm_client_init
#define nouveau_client_fini nvkm_client_fini
#define nouveau_engctx nvkm_engctx
#define nouveau_engctx_create nvkm_engctx_create
#define nouveau_engctx_create_ nvkm_engctx_create_
#define nouveau_engctx_destroy nvkm_engctx_destroy
#define nouveau_engctx_init nvkm_engctx_init
#define nouveau_engctx_fini nvkm_engctx_fini
#define _nouveau_engctx_ctor _nvkm_engctx_ctor
#define _nouveau_engctx_dtor _nvkm_engctx_dtor
#define _nouveau_engctx_init _nvkm_engctx_init
#define _nouveau_engctx_fini _nvkm_engctx_fini
#define _nouveau_engctx_rd32 _nvkm_engctx_rd32
#define _nouveau_engctx_wr32 _nvkm_engctx_wr32
#define nouveau_engctx_get nvkm_engctx_get
#define nouveau_engctx_put nvkm_engctx_put
#define nouveau_engine nvkm_engine
#define nouveau_engine_create nvkm_engine_create
#define nouveau_engine_create_ nvkm_engine_create_
#define nouveau_engine_destroy nvkm_engine_destroy
#define nouveau_engine_init nvkm_engine_init
#define nouveau_engine_fini nvkm_engine_fini
#define _nouveau_engine_ctor _nvkm_engine_ctor
#define _nouveau_engine_dtor _nvkm_engine_dtor
#define _nouveau_engine_init _nvkm_engine_init
#define _nouveau_engine_fini _nvkm_engine_fini
#define nouveau_enum nvkm_enum
#define nouveau_gpuobj nvkm_gpuobj
#define nouveau_gpuobj_create nvkm_gpuobj_create
#define nouveau_gpuobj_destroy nvkm_gpuobj_destroy
#define _nouveau_gpuobj_ctor _nvkm_gpuobj_ctor
#define _nouveau_gpuobj_dtor _nvkm_gpuobj_dtor
#define _nouveau_gpuobj_init _nvkm_gpuobj_init
#define _nouveau_gpuobj_fini _nvkm_gpuobj_fini
#define _nouveau_gpuobj_rd32 _nvkm_gpuobj_rd32
#define _nouveau_gpuobj_wr32 _nvkm_gpuobj_wr32
#define nouveau_gpuobj_new nvkm_gpuobj_new
#define nouveau_gpuobj_dup nvkm_gpuobj_dup
#define nouveau_gpuobj_ref nvkm_gpuobj_ref
#define nouveau_gpuobj_map nvkm_gpuobj_map
#define nouveau_gpuobj_map_vm nvkm_gpuobj_map_vm
#define nouveau_gpuobj_unmap nvkm_gpuobj_unmap
#define nouveau_handle nvkm_handle
#define nouveau_handle_ref nvkm_handle_ref
#define nouveau_handle_put nvkm_handle_put
#define nouveau_handle_get_class nvkm_handle_get_class
#define nouveau_handle_get_vinst nvkm_handle_get_vinst
#define nouveau_handle_get_cinst nvkm_handle_get_cinst
#define nouveau_mm nvkm_mm
#define nouveau_mm_node nvkm_mm_node
#define nouveau_mm_init nvkm_mm_init
#define nouveau_mm_fini nvkm_mm_fini
#define nouveau_mm_head nvkm_mm_head
#define nouveau_mm_tail nvkm_mm_tail
#define nouveau_mm_free nvkm_mm_free
#define nouveau_mm_initialised nvkm_mm_initialised
#define nouveau_namedb nvkm_namedb
#define nouveau_namedb_create nvkm_namedb_create
#define nouveau_namedb_create_ nvkm_namedb_create_
#define nouveau_namedb_destroy nvkm_namedb_destroy
#define nouveau_namedb_init nvkm_namedb_init
#define nouveau_namedb_fini nvkm_namedb_fini
#define _nouveau_namedb_ctor _nvkm_namedb_ctor
#define _nouveau_namedb_dtor _nvkm_namedb_dtor
#define _nouveau_namedb_init _nvkm_namedb_init
#define _nouveau_namedb_fini _nvkm_namedb_fini
#define nouveau_namedb_ref nvkm_namedb_ref
#define nouveau_namedb_put nvkm_namedb_put
#define nouveau_namedb_get nvkm_namedb_get
#define nouveau_namedb_get_class nvkm_namedb_get_class
#define nouveau_namedb_get_vinst nvkm_namedb_get_vinst
#define nouveau_namedb_get_cinst nvkm_namedb_get_cinst
#define nouveau_object_debug nvkm_object_debug
#define nouveau_object nvkm_object
#define nouveau_object_create nvkm_object_create
#define nouveau_object_create_ nvkm_object_create_
#define nouveau_object_destroy nvkm_object_destroy
#define nouveau_object_init nvkm_object_init
#define nouveau_object_fini nvkm_object_fini
#define _nouveau_object_ctor _nvkm_object_ctor
#define nouveau_object_ctor nvkm_object_ctor
#define nouveau_object_ref nvkm_object_ref
#define nouveau_object_ofuncs nvkm_object_ofuncs
#define nouveau_object_inc nvkm_object_inc
#define nouveau_object_dec nvkm_object_dec
#define nouveau_ofuncs nvkm_ofuncs
#define nouveau_oclass nvkm_oclass
#define nouveau_omthds nvkm_omthds
#define nouveau_parent nvkm_parent
#define nouveau_parent_create nvkm_parent_create
#define nouveau_parent_create_ nvkm_parent_create_
#define nouveau_parent_destroy nvkm_parent_destroy
#define nouveau_parent_init nvkm_parent_init
#define nouveau_parent_fini nvkm_parent_fini
#define _nouveau_parent_ctor _nvkm_parent_ctor
#define _nouveau_parent_dtor _nvkm_parent_dtor
#define _nouveau_parent_init _nvkm_parent_init
#define _nouveau_parent_fini _nvkm_parent_fini
#define nouveau_printk nvkm_printk
#define nouveau_ramht nvkm_ramht
#define nouveau_ramht_new nvkm_ramht_new
#define nouveau_ramht_ref nvkm_ramht_ref
#define nouveau_ramht_insert nvkm_ramht_insert
#define nouveau_ramht_remove nvkm_ramht_remove
#define nouveau_subdev nvkm_subdev
#define nouveau_subdev_create nvkm_subdev_create
#define nouveau_subdev_create_ nvkm_subdev_create_
#define nouveau_subdev_destroy nvkm_subdev_destroy
#define nouveau_subdev_init nvkm_subdev_init
#define nouveau_subdev_fini nvkm_subdev_fini
#define _nouveau_subdev_ctor _nvkm_subdev_ctor
#define _nouveau_subdev_dtor _nvkm_subdev_dtor
#define _nouveau_subdev_init _nvkm_subdev_init
#define _nouveau_subdev_fini _nvkm_subdev_fini
#define nouveau_subdev_reset nvkm_subdev_reset
#define nouveau_bitfield nvkm_bitfield
#define nouveau_bitfield_print nvkm_bitfield_print
#define nouveau_enum nvkm_enum
#define nouveau_enum_find nvkm_enum_find
#define nouveau_enum_print nvkm_enum_print
#define nouveau_stropt nvkm_stropt
#define nouveau_boolopt nvkm_boolopt
#define nouveau_dbgopt nvkm_dbgopt
#define nouveau_device nvkm_device
#define nouveau_device_find nvkm_device_find
#define nouveau_device_list nvkm_device_list
#define nouveau_vma nvkm_vma
#define nouveau_vm nvkm_vm
#define nouveau_vm_get nvkm_vm_get
#define nouveau_vm_put nvkm_vm_put
#define nouveau_vm_map nvkm_vm_map
#define nouveau_vm_unmap nvkm_vm_unmap
#define nouveau_vm_new nvkm_vm_new
#define nouveau_vm_ref nvkm_vm_ref
#define nouveau_instmem nvkm_instmem
#define nouveau_instobj nvkm_instobj
#define nouveau_mem nvkm_mem
#define nouveau_bar nvkm_bar
#define nouveau_falcon nvkm_falcon
#define nouveau_falcon_create nvkm_falcon_create
#define nouveau_falcon_create_ nvkm_falcon_create_
#define nouveau_falcon_destroy nvkm_falcon_destroy
#define nouveau_falcon_init nvkm_falcon_init
#define nouveau_falcon_fini nvkm_falcon_fini
#define _nouveau_falcon_ctor _nvkm_falcon_ctor
#define _nouveau_falcon_dtor _nvkm_falcon_dtor
#define _nouveau_falcon_init _nvkm_falcon_init
#define _nouveau_falcon_fini _nvkm_falcon_fini
#define _nouveau_falcon_rd32 _nvkm_falcon_rd32
#define _nouveau_falcon_wr32 _nvkm_falcon_wr32
#define nouveau_falcon_context nvkm_falcon_context
#define nouveau_falcon_context_create nvkm_falcon_context_create
#define nouveau_falcon_context_create_ nvkm_falcon_context_create_
#define nouveau_falcon_context_destroy nvkm_falcon_context_destroy
#define nouveau_falcon_context_init nvkm_falcon_context_init
#define nouveau_falcon_context_fini nvkm_falcon_context_fini
#define _nouveau_falcon_context_ctor _nvkm_falcon_context_ctor
#define _nouveau_falcon_context_dtor _nvkm_falcon_context_dtor
#define _nouveau_falcon_context_init _nvkm_falcon_context_init
#define _nouveau_falcon_context_fini _nvkm_falcon_context_fini
#define _nouveau_falcon_context_rd32 _nvkm_falcon_context_rd32
#define _nouveau_falcon_context_wr32 _nvkm_falcon_context_wr32
#define nouveau_falcon_intr nvkm_falcon_intr
#define nouveau_xtensa nvkm_xtensa
#define nouveau_xtensa_create nvkm_xtensa_create
#define nouveau_xtensa_create_ nvkm_xtensa_create_
#define nouveau_xtensa_destroy nvkm_xtensa_destroy
#define nouveau_xtensa_init nvkm_xtensa_init
#define nouveau_xtensa_fini nvkm_xtensa_fini
#define _nouveau_xtensa_ctor _nvkm_xtensa_ctor
#define _nouveau_xtensa_dtor _nvkm_xtensa_dtor
#define _nouveau_xtensa_init _nvkm_xtensa_init
#define _nouveau_xtensa_fini _nvkm_xtensa_fini
#define _nouveau_xtensa_rd32 _nvkm_xtensa_rd32
#define _nouveau_xtensa_wr32 _nvkm_xtensa_wr32
#define nouveau_xtensa_context nvkm_xtensa_context
#define nouveau_xtensa_context_create nvkm_xtensa_context_create
#define nouveau_xtensa_context_create_ nvkm_xtensa_context_create_
#define nouveau_xtensa_context_destroy nvkm_xtensa_context_destroy
#define nouveau_xtensa_context_init nvkm_xtensa_context_init
#define nouveau_xtensa_context_fini nvkm_xtensa_context_fini
#define _nouveau_xtensa_engctx_ctor _nvkm_xtensa_engctx_ctor
#define _nouveau_xtensa_context_dtor _nvkm_xtensa_context_dtor
#define _nouveau_xtensa_context_init _nvkm_xtensa_context_init
#define _nouveau_xtensa_context_fini _nvkm_xtensa_context_fini
#define _nouveau_xtensa_context_rd32 _nvkm_xtensa_context_rd32
#define _nouveau_xtensa_context_wr32 _nvkm_xtensa_context_wr32
#define nouveau_xtensa_intr nvkm_xtensa_intr
#define nouveau_gpio nvkm_gpio
#define nouveau_i2c nvkm_i2c
#define nouveau_i2c_port nvkm_i2c_port
#define nouveau_i2c_board_info nvkm_i2c_board_info
#define nouveau_devinit nvkm_devinit
#define nouveau_bios nvkm_bios
#define nouveau_bios_oclass nvkm_bios_oclass
#define nouveau_pll_vals nvkm_pll_vals
#define nouveau_therm_trip_point nvkm_therm_trip_point
#define nouveau_fb nvkm_fb
#define nouveau_fifo nvkm_fifo
#define nouveau_therm nvkm_therm
#define nouveau_therm_cstate nvkm_therm_cstate
#define nouveau_volt nvkm_volt
#define nouveau_timer nvkm_timer
#define nouveau_timer_wait_eq nvkm_timer_wait_eq
#define nouveau_timer_alarm nvkm_timer_alarm
#define nouveau_alarm nvkm_alarm
#define nouveau_timer_alarm_cancel nvkm_timer_alarm_cancel
#define nouveau_alarm_init nvkm_alarm_init
#define nva3_pll_calc gt215_pll_calc
#define nouveau_clk nvkm_clk
#define nouveau_domain nvkm_domain
#define nouveau_cstate nvkm_cstate
#define nouveau_pstate nvkm_pstate
#define nouveau_clk_astate nvkm_clk_astate
#define nouveau_clk_ustate nvkm_clk_ustate
#define nva3_clk_pre gt215_clk_pre
#define nva3_clk_post gt215_clk_post
#define nva3_clk_info gt215_clk_info
#define nva3_pll_info gt215_pll_info
#define nouveau_ibus nvkm_ibus
#define nouveau_memx nvkm_memx
#define nouveau_memx_block nvkm_memx_block
#define nouveau_memx_unblock nvkm_memx_unblock
#define nouveau_memx_train nvkm_memx_train
#define nouveau_memx_train_result nvkm_memx_train_result
#define nouveau_memx_wait_vblank nvkm_memx_wait_vblank
#define nouveau_memx_rd32 nvkm_memx_rd32
#define nouveau_memx_wr32 nvkm_memx_wr32
#define nouveau_memx_wait nvkm_memx_wait
#define nouveau_memx_init nvkm_memx_init
#define nouveau_memx_fini nvkm_memx_fini
#define nouveau_memx_nsec nvkm_memx_nsec
#define nouveau_ltc nvkm_ltc
#define nouveau_pmu nvkm_pmu
#define nouveau_fb nvkm_fb
#define nouveau_fb_tile nvkm_fb_tile
#define nvc0_pte_storage_type_map gf100_pte_storage_type_map
#define nouveau_fuse nvkm_fuse
#define nouveau_mc nvkm_mc
#define nouveau_mmu nvkm_mmu

#endif
