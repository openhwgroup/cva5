// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM___024ROOT_H_
#define VERILATED_VTAIGA_SIM___024ROOT_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;
class Vtaiga_sim_axi_interface;
class Vtaiga_sim_l2_requester_interface;
class Vtaiga_sim_l2_memory_interface;
class Vtaiga_sim_l2_arbitration_interface;
class Vtaiga_sim_fifo_interface__D2b;
class Vtaiga_sim_fifo_interface__D20;
class Vtaiga_sim_fifo_interface__D1e;
class Vtaiga_sim_fifo_interface__D22;
class Vtaiga_sim_fifo_interface__D2c;
class Vtaiga_sim_fifo_interface__D7;
class Vtaiga_sim_fifo_interface__D23;
class Vtaiga_sim_lfsr__W4;
class Vtaiga_sim_branch_predictor_interface;
class Vtaiga_sim_ras_interface;
class Vtaiga_sim_register_file_issue_interface__pi1;
class Vtaiga_sim_fp_register_file_issue_interface;
class Vtaiga_sim_unit_issue_interface;
class Vtaiga_sim_unit_writeback_interface;
class Vtaiga_sim_fp_unit_writeback_interface;
class Vtaiga_sim_tlb_interface;
class Vtaiga_sim_renamer_interface__N2;
class Vtaiga_sim_fp_renamer_interface;
class Vtaiga_sim_exception_interface;
class Vtaiga_sim_fifo_interface__D4;
class Vtaiga_sim_fetch_sub_unit_interface__pi5;
class Vtaiga_sim_fifo_interface__D5;
class Vtaiga_sim_fifo_interface__D3;
class Vtaiga_sim_fifo_interface__D6;
class Vtaiga_sim_fifo_interface__D12;
class Vtaiga_sim_ls_sub_unit_interface__pi11;
class Vtaiga_sim_ls_sub_unit_interface__pi12;
class Vtaiga_sim_fifo_interface__Db;
class Vtaiga_sim_load_store_queue_interface;
class Vtaiga_sim_unsigned_division_interface;
class Vtaiga_sim_fifo_interface__D52;
class Vtaiga_sim_clz_tree;
class Vtaiga_sim_fifo_interface__D110;
class Vtaiga_sim_fifo_interface__D54;
class Vtaiga_sim_unsigned_sqrt_interface__D38;
class Vtaiga_sim_fifo_interface__Db0;
class Vtaiga_sim_unsigned_division_interface__pi16;


class Vtaiga_sim___024root final : public VerilatedModule {
  public:
    // CELLS
    Vtaiga_sim_axi_interface* __PVT__taiga_sim__DOT__m_axi;
    Vtaiga_sim_l2_requester_interface* __PVT__taiga_sim__DOT__l2__BRA__1__KET__;
    Vtaiga_sim_l2_requester_interface* __PVT__taiga_sim__DOT__l2__BRA__0__KET__;
    Vtaiga_sim_l2_memory_interface* __PVT__taiga_sim__DOT__mem;
    Vtaiga_sim_l2_arbitration_interface* __PVT__taiga_sim__DOT__l2_arb__DOT__arb;
    Vtaiga_sim_fifo_interface__D2b* __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__1__KET__;
    Vtaiga_sim_fifo_interface__D2b* __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D20* __PVT__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__1__KET__;
    Vtaiga_sim_fifo_interface__D20* __PVT__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D1e* __PVT__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__1__KET__;
    Vtaiga_sim_fifo_interface__D1e* __PVT__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D22* __PVT__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__1__KET__;
    Vtaiga_sim_fifo_interface__D22* __PVT__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D2c* __PVT__taiga_sim__DOT__l2_arb__DOT__mem_addr_fifo;
    Vtaiga_sim_fifo_interface__D20* __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo;
    Vtaiga_sim_fifo_interface__D7* __PVT__taiga_sim__DOT__l2_arb__DOT__data_attributes;
    Vtaiga_sim_fifo_interface__D23* __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata_fifo;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_branch_predictor_interface* __PVT__taiga_sim__DOT__cpu__DOT__bp;
    Vtaiga_sim_ras_interface* __PVT__taiga_sim__DOT__cpu__DOT__ras;
    Vtaiga_sim_register_file_issue_interface__pi1* __PVT__taiga_sim__DOT__cpu__DOT__rf_issue;
    Vtaiga_sim_fp_register_file_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fp_rf_issue;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__10__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__9__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__8__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__7__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__6__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__5__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__4__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__3__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__2__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__1__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__0__KET__;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET__;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__3__KET__;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__2__KET__;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__1__KET__;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__0__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__1__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__0__KET__;
    Vtaiga_sim_tlb_interface* __PVT__taiga_sim__DOT__cpu__DOT__itlb;
    Vtaiga_sim_tlb_interface* __PVT__taiga_sim__DOT__cpu__DOT__dtlb;
    Vtaiga_sim_renamer_interface__N2* __PVT__taiga_sim__DOT__cpu__DOT__decode_rename_interface;
    Vtaiga_sim_fp_renamer_interface* __PVT__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface;
    Vtaiga_sim_exception_interface* __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__2__KET__;
    Vtaiga_sim_exception_interface* __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__1__KET__;
    Vtaiga_sim_exception_interface* __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D4* __PVT__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__oldest_fp_issued_fifo;
    Vtaiga_sim_fetch_sub_unit_interface__pi5* __PVT__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram;
    Vtaiga_sim_fifo_interface__D5* __PVT__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo;
    Vtaiga_sim_fifo_interface__D3* __PVT__taiga_sim__DOT__cpu__DOT__ras_block__DOT__ri_fifo;
    Vtaiga_sim_fifo_interface__D6* __PVT__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list;
    Vtaiga_sim_fifo_interface__D12* __PVT__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list;
    Vtaiga_sim_fifo_interface__D6* __PVT__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list;
    Vtaiga_sim_fifo_interface__D12* __PVT__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list;
    Vtaiga_sim_ls_sub_unit_interface__pi11* __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bram;
    Vtaiga_sim_ls_sub_unit_interface__pi12* __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bus;
    Vtaiga_sim_fifo_interface__Db* __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes;
    Vtaiga_sim_load_store_queue_interface* __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq;
    Vtaiga_sim_fifo_interface__D2c* __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_fifo;
    Vtaiga_sim_unsigned_division_interface* __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div;
    Vtaiga_sim_fifo_interface__D52* __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo;
    Vtaiga_sim_fifo_interface__D20* __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__wb_fifo;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__3__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__2__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__1__KET__;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__0__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__2__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__1__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__0__KET__;
    Vtaiga_sim_clz_tree* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz;
    Vtaiga_sim_clz_tree* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__mul_issue;
    Vtaiga_sim_fifo_interface__D110* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__add_issue;
    Vtaiga_sim_clz_tree* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz;
    Vtaiga_sim_clz_tree* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_issue;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_issue;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_wb;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb;
    Vtaiga_sim_fifo_interface__D54* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo;
    Vtaiga_sim_unsigned_sqrt_interface__D38* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt;
    Vtaiga_sim_fifo_interface__Db0* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo;
    Vtaiga_sim_unsigned_division_interface__pi16* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened;
    Vtaiga_sim_clz_tree* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__i2f_issue;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__minmax_issue;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__sign_inj_issue;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__i2f_wb;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__minmax_wb;
    Vtaiga_sim_fp_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__sign_inj_wb;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_issue;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_issue;
    Vtaiga_sim_unit_issue_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_issue;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_wb;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_wb;
    Vtaiga_sim_unit_writeback_interface* __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_wb;

    // DESIGN SPECIFIC STATE
    // Anonymous structures to workaround compiler member-count bugs
    struct {
        VL_IN8(clk,0,0);
        VL_IN8(rst,0,0);
        VL_OUT8(ddr_axi_arburst,1,0);
        VL_OUT8(ddr_axi_arcache,3,0);
        VL_OUT8(ddr_axi_arid,5,0);
        VL_OUT8(ddr_axi_arlen,7,0);
        VL_OUT8(ddr_axi_arlock,0,0);
        VL_OUT8(ddr_axi_arprot,2,0);
        VL_OUT8(ddr_axi_arqos,3,0);
        VL_IN8(ddr_axi_arready,0,0);
        VL_OUT8(ddr_axi_arregion,3,0);
        VL_OUT8(ddr_axi_arsize,2,0);
        VL_OUT8(ddr_axi_arvalid,0,0);
        VL_OUT8(ddr_axi_awburst,1,0);
        VL_OUT8(ddr_axi_awcache,3,0);
        VL_OUT8(ddr_axi_awid,5,0);
        VL_OUT8(ddr_axi_awlen,7,0);
        VL_OUT8(ddr_axi_awlock,0,0);
        VL_OUT8(ddr_axi_awprot,2,0);
        VL_OUT8(ddr_axi_awqos,3,0);
        VL_IN8(ddr_axi_awready,0,0);
        VL_OUT8(ddr_axi_awregion,3,0);
        VL_OUT8(ddr_axi_awsize,2,0);
        VL_OUT8(ddr_axi_awvalid,0,0);
        VL_OUT8(ddr_axi_bid,5,0);
        VL_OUT8(ddr_axi_bready,0,0);
        VL_IN8(ddr_axi_bresp,1,0);
        VL_IN8(ddr_axi_bvalid,0,0);
        VL_IN8(ddr_axi_rid,5,0);
        VL_IN8(ddr_axi_rlast,0,0);
        VL_OUT8(ddr_axi_rready,0,0);
        VL_IN8(ddr_axi_rresp,1,0);
        VL_IN8(ddr_axi_rvalid,0,0);
        VL_OUT8(ddr_axi_wlast,0,0);
        VL_IN8(ddr_axi_wready,0,0);
        VL_OUT8(ddr_axi_wstrb,3,0);
        VL_OUT8(ddr_axi_wvalid,0,0);
        VL_OUT8(ddr_axi_wid,5,0);
        VL_IN8(be,3,0);
        VL_IN8(rnw,0,0);
        VL_IN8(is_amo,0,0);
        VL_IN8(amo_type_or_burst_size,4,0);
        VL_IN8(sub_id,1,0);
        VL_IN8(request_push,0,0);
        VL_OUT8(request_full,0,0);
        VL_OUT8(inv_valid,0,0);
        VL_IN8(inv_ack,0,0);
        VL_OUT8(con_result,0,0);
        VL_OUT8(con_valid,0,0);
        VL_IN8(wr_data_push,0,0);
        VL_OUT8(data_full,0,0);
        VL_OUT8(rd_sub_id,1,0);
        VL_OUT8(rd_data_valid,0,0);
        VL_IN8(rd_data_ack,0,0);
        VL_OUT8(instruction_bram_en,0,0);
        VL_OUT8(instruction_bram_be,3,0);
        VL_OUT8(data_bram_we,1,0);
        VL_OUT8(data_bram_en,0,0);
        VL_OUT8(data_bram_be,3,0);
        VL_OUT8(write_uart,0,0);
        VL_OUT8(uart_byte,7,0);
        VL_OUT8(store_queue_empty,0,0);
        VL_OUT8(load_store_idle,0,0);
        VL_OUT8(instruction_issued,0,0);
    };
    struct {
        CData/*0:0*/ taiga_sim__DOT__axi_arvalid;
        CData/*5:0*/ taiga_sim__DOT__axi_awid;
        CData/*0:0*/ taiga_sim__DOT__axi_awvalid;
        CData/*0:0*/ taiga_sim__DOT__axi_wlast;
        CData/*0:0*/ taiga_sim__DOT__axi_wvalid;
        CData/*3:0*/ taiga_sim__DOT__read_counter;
        CData/*0:0*/ taiga_sim__DOT__begin_read_counter;
        CData/*3:0*/ taiga_sim__DOT__write_counter;
        CData/*0:0*/ taiga_sim__DOT__begin_write_counter;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fp_unit_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fp_no_id_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fp_no_instruction_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fp_other_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fls_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fdiv_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fsqrt_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fcmp_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fsign_inject_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fclass_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fcvt_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fls;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fmadd;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fdiv_sqrt;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_wb2fp;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fmadd_stall_due_to_fmadd;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs1;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs2;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs3;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall_rs1;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall_rs2;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall_rs1;
        CData/*0:0*/ taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall_rs2;
        CData/*1:0*/ taiga_sim__DOT__fpu_tracer__DOT__fp_units_pending_wb;
        CData/*3:0*/ taiga_sim__DOT__fpu_tracer__DOT__unit_done_r;
        CData/*3:0*/ taiga_sim__DOT__fpu_tracer__DOT__unit_done_r_r;
        CData/*0:0*/ taiga_sim__DOT__l2_to_mem__DOT__read_modify_write;
        CData/*0:0*/ taiga_sim__DOT__l2_to_mem__DOT__address_phase_complete;
        CData/*1:0*/ taiga_sim__DOT__l2_to_mem__DOT__read_count;
        CData/*0:0*/ taiga_sim__DOT__l2_to_mem__DOT__amo_write_ready;
        CData/*4:0*/ taiga_sim__DOT__l2_to_mem__DOT__write_reference_burst_count;
        CData/*0:0*/ taiga_sim__DOT__l2_to_mem__DOT__write_in_progress;
        CData/*0:0*/ taiga_sim__DOT__l2_to_mem__DOT__write_transfer_complete;
        CData/*0:0*/ taiga_sim__DOT__l2_to_mem__DOT__pop;
        CData/*4:0*/ taiga_sim__DOT__l2_to_mem__DOT__write_burst_count;
        CData/*0:0*/ taiga_sim__DOT__l2_to_mem__DOT__on_last_burst;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__advance;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__reserv_valid;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__reserv_lr;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__reserv_sc;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__reserv_store;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__reserv_id;
        CData/*1:0*/ taiga_sim__DOT__l2_arb__DOT__reserv_id_v;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__write_done;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__burst_count;
        CData/*1:0*/ taiga_sim__DOT__l2_arb__DOT__return_push;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT____Vcellout__reserv__abort;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__rr__DOT__state;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*1:0*/ taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation;
        CData/*1:0*/ taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match;
    };
    struct {
        CData/*1:0*/ taiga_sim__DOT__l2_arb__DOT__reserv__DOT__revoke_reservation;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_index;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index;
        CData/*5:0*/ taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*6:0*/ taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
        CData/*1:0*/ taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback;
        CData/*1:0*/ taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_flush;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__pc_id;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__pc_id_assigned;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fetch_id;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fetch_complete;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__early_branch_flush;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_advance;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__decode_exception_unit;
        CData/*7:0*/ taiga_sim__DOT__cpu__DOT__retire;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_idle;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__post_issue_count;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__interrupt_taken;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__interrupt_pending;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__instruction_issued;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__instruction_issued_with_rd;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_instruction_issued_with_rd;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_operand_stall;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_unit_stall;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_no_id_stall;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_no_instruction_stall;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_alu_op;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_branch_or_jump_op;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_load_op;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_store_op;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_mul_op;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_div_op;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_misc_op;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_rs1_forwarding_needed;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_rs2_forwarding_needed;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__tr_rs1_and_rs2_forwarding_needed;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__oldest_pre_issue_id;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__fetched_count_neg;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__pre_issue_count;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__pre_issue_count_next;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__post_issue_count_next;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__inflight_count;
        CData/*7:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_wb2_float;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_wb2_float;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_accu_fcsr;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__encoder_rom;
    };
    struct {
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_wb2_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_is_float;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_accu_fcsr;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_index;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__sub_unit_address_match;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_next;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__flush_or_rst;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__update_pc;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__exception_pending;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__valid_fetch_result;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__encoder_rom;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_if;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__replacement_way;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_update_way;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__target_update_way;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__new_index;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT____Vcellinp__read_index_fifo__rst;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_index;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rename_valid;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rollback;
        CData/*6:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_previous_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_update;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__write_index;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__read_index;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rename_valid;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rollback;
        CData/*6:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_previous_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_update;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__write_index;
    };
    struct {
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__read_index;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__inflight_count;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__uses_rd;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fence;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_ifence;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_i2f;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_f2i;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_class;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fcmp;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_valid;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__operands_ready;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_operands_ready;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__pre_issue_exception_pending;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__illegal_instruction_pattern;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_stage_ready;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_rs_wb_group;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_imm_type;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_op;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_op_r;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_logic_op_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_subtract;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_load_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_store_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fence_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rs1_link;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rd_link;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_return;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_call;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__br_use_signed;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__jalr;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_mret_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_sret_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_ifence_r;
        CData/*7:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__genblk6__DOT__prev_div_rs_addr;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__genblk6__DOT__prev_div_result_valid;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_sign_inj;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_sign_inj_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_minmax;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_minmax_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_class_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_f2i_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_fcmp_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__uses_rs1;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_issue_rs_wb_group;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_issued_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_taken;
    };
    struct {
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_taken_ex;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__id_ex;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__instruction_is_completing;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__jal_jalr_ex;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__is_return;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__is_call;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_switch_stall;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__ready_for_issue_from_lsq;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__issue_request;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_ready;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_valid;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__last_unit;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unaligned_addr;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_exception_complete;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__fence_hold;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_ack;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_full;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_conflict;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_ack;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_output_valid;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__rst;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_index;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__inflight_count;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid_next;
        SData/*15:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__hashes;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__released;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__id_needed;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index_next;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_request_one_hot;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__issued_one_hot;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_sq_request;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h0412e4c3__0;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_hc604ed0f__0;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT__ready;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT____Vcellout__arvalid_m__result;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT____Vcellout__awvalid_m__result;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT____Vcellout__wvalid_m__result;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__busy;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__commit;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__commit_in_progress;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_inc;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_inc;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_frm;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_init_clear;
    };
    struct {
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_fetch_hold;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_issue_hold;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc_override;
        CData/*6:0*/ taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state_counter;
        VlWide<3>/*95:0*/ taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__stage1_advance;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__stage2_advance;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ;
        CData/*7:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress_attr;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div_ready;
        CData/*7:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz;
        CData/*7:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__CLZ_delta;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__first_cycle_abort;
        CData/*1:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__new_quotient_bits;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_1x_overflow;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__cycles_remaining;
        CData/*3:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__cycles_remaining_next;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__running;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_i2f;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_f2i;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_class;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fcmp;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_minmax;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_sign_inj;
        CData/*6:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_opcode;
        CData/*6:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_fn7;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_issue_id;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_swap;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_hidden_bit_pre_normalized;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_hidden_bit_pre_normalized;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_fadd;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_fmul;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fma;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fadd;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fmul;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_add;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_sign;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_zero;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_int_less_than_1;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_31;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_30;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__adder_carry_out;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__r_adder_carry_out;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_QNaN;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_inf;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rm;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__in_progress;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT____Vcellinp__in_progress_m__set;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__in_progress_attr;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__done_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__running;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__terminate;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__running;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__start_algorithm;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT____Vcellinp__in_progress_m__set;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__start_algorithm_r;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__id_in_progress;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_hidden_bit;
    };
    struct {
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_hidden_bit;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_normal;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_normal;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rm;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_inf;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_SNaN;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_QNaN;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_zero;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_inf;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_SNaN;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_QNaN;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_zero;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__early_terminate;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_QNaN;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_inf;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__advance;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__terminate;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__advance;
        CData/*4:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz;
        CData/*7:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__instruction;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__advance;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__id;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__done;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__grs;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_inexact;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__roundup;
        CData/*5:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__largest_unsigned_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__largest_signed_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__greater_than_largest_unsigned_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_greater_than_largest_unsigned_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__greater_than_largest_signed_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_greater_than_largest_signed_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smaller_than_smallest_signed_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_smaller_than_smallest_signed_int;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_special;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_subtract;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__r_invalid_cmp;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__unordered;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__flt;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__feq;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__r_result;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__done;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__id;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__sign_equ;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__done;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__done_r;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__id;
        CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__id_r;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_norm;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_shift;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_round;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vlvbound_he380f72e__0;
        CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT____Vlvbound_he380f72e__0;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom;
        CData/*3:0*/ __Vdly__taiga_sim__DOT__read_counter;
        CData/*0:0*/ __Vdly__taiga_sim__DOT__begin_read_counter;
        CData/*3:0*/ __Vdly__taiga_sim__DOT__write_counter;
        CData/*0:0*/ __Vdly__taiga_sim__DOT__begin_write_counter;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table__v1;
        CData/*1:0*/ __Vdly__taiga_sim__DOT__l2_to_mem__DOT__read_count;
        CData/*0:0*/ __Vdly__taiga_sim__DOT__axi_arvalid;
    };
    struct {
        CData/*4:0*/ __Vdly__taiga_sim__DOT__l2_to_mem__DOT__write_burst_count;
        CData/*4:0*/ __Vdly__taiga_sim__DOT__l2_arb__DOT__burst_count;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation_address__v0;
        CData/*4:0*/ __Vdly__taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index;
        CData/*4:0*/ __Vdly__taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_index;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*4:0*/ __Vdly__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__inflight_count;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__fetch_metadata_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__uses_rd_table__v0;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__id_block__DOT__oldest_pre_issue_id;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__pc_id;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__fetch_id;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__accu_fcsr_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_float_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__is_float_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_int_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__need_int_data_table__v0;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_index;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__0__KET____DOT__tag_bank__DOT__branch_ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__1__KET____DOT__tag_bank__DOT__branch_ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__0__KET____DOT__addr_table__DOT__branch_ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__1__KET____DOT__addr_table__DOT__branch_ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram__v0;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_index;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__lut_ram__v0;
        CData/*4:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index;
        CData/*4:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__lut_ram__v0;
        CData/*4:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index;
        CData/*4:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rd_to_id_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rd_to_id_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse_r__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__1__KET____DOT__reg_group__DOT__register_file_bank__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse_r__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank__v0;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index;
        CData/*2:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_index;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_attr__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_issue__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb__v0;
    };
    struct {
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_issue__v0;
        CData/*6:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state_counter;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__mulh__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__mulh__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__id__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__id__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_frac__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_frac__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__possible_subnormal__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_expo__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_expo__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_sign__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_sign__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_frac__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_frac__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__instruction__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_expo__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_expo__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_sign__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_sign__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf__v3;
    };
    struct {
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__right_shift__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__zero_result_sign__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__special_case_results__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf__v3;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm__v1;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm__v2;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs_sticky_bit__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_sign__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo_overflow__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_sign__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__special_case_results__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__unit_fflags_table__v0;
        CData/*0:0*/ __Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__fp_unit_fflags_table__v0;
        CData/*0:0*/ __Vclklast__TOP__clk;
        SData/*8:0*/ taiga_sim__DOT__cpu__DOT__fp_unit_fflag_wb_packet;
        SData/*8:0*/ taiga_sim__DOT__cpu__DOT__unit_fflag_wb_packet;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__ls_offset;
    };
    struct {
        SData/*15:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a;
        SData/*15:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b;
        SData/*15:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes_in;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__expo_diff;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_expo_diff;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_expo_diff_negate;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_pre_normalize_shift_amt;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_pre_normalize_shift_amt;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_rs1_expo_unbiased;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__clz_with_prepended_0s;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__clz_with_prepended_0s;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__clz_with_prepended_0s;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__clz_with_prepended_0s;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo_r;
        SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_left_shift_amt;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_left_shift_amt;
        SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__clz_with_prepended_0s;
        SData/*8:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR;
        SData/*8:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs;
        VL_OUT(ddr_axi_araddr,31,0);
        VL_OUT(ddr_axi_awaddr,31,0);
        VL_IN(ddr_axi_rdata,31,0);
        VL_OUT(ddr_axi_wdata,31,0);
        VL_IN(addr,29,0);
        VL_OUT(inv_addr,31,2);
        VL_IN(wr_data,31,0);
        VL_OUT(rd_data,31,0);
        VL_OUT(instruction_bram_addr,29,0);
        VL_OUT(instruction_bram_data_in,31,0);
        VL_IN(instruction_bram_data_out,31,0);
        VL_OUT(data_bram_addr,28,0);
        VL_OUT(NUM_RETIRE_PORTS,31,0);
        VL_OUT(instruction_pc_dec,31,0);
        VL_OUT(instruction_data_dec,31,0);
        IData/*31:0*/ taiga_sim__DOT__l2_to_mem__DOT__amo_result;
        IData/*31:0*/ taiga_sim__DOT__l2_to_mem__DOT__amo_result_r;
        IData/*31:0*/ taiga_sim__DOT__l2_arb__DOT__mem_data__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fetch_instruction;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__epc;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__exception_target_pc;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__next_pc;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc;
        QData/*45:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry;
        IData/*22:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__predicted_pc;
        IData/*22:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk1__DOT__branch_tag_banks__BRA__0__KET____DOT__tag_bank__read_data;
        IData/*22:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk1__DOT__branch_tag_banks__BRA__1__KET____DOT__tag_bank__read_data;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk2__DOT__branch_table_banks__BRA__0__KET____DOT__addr_table__read_data;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk2__DOT__branch_table_banks__BRA__1__KET____DOT__addr_table__read_data;
        IData/*17:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
        IData/*17:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu;
        IData/*20:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__pc_offset_r;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc_ex;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__pc_ex;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellout__genblk4__DOT__genblk1__DOT__axi_bus__data_out;
    };
    struct {
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__selected_csr;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__selected_csr_r;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__fcsr;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_fcsr;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__shifted_divisor;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_1x;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_int_rs1;
        VlWide<4>/*105:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac_intermediate;
        VlWide<4>/*103:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_in;
        VlWide<4>/*103:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs;
        VlWide<4>/*103:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_intermediate;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__counter;
        VlWide<4>/*108:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__shift_count;
        VlWide<3>/*83:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_f2i_int;
        IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_in1;
        VlWide<5>/*158:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout;
        VlWide<5>/*158:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout;
        IData/*31:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__counter;
        VL_OUT64(data_bram_data_in,63,0);
        VL_IN64(data_bram_data_out,63,0);
        VL_IN64(debug_instructions,63,0);
        VlWide<3>/*89:0*/ taiga_sim__DOT__tr;
        VlWide<3>/*84:0*/ taiga_sim__DOT__fp_tr;
        QData/*42:0*/ taiga_sim__DOT__l2_arb__DOT__arb_request;
        QData/*42:0*/ taiga_sim__DOT__l2_arb__DOT__reserv_request;
        QData/*43:0*/ taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
        VlWide<3>/*71:0*/ taiga_sim__DOT__cpu__DOT__br_results;
        VlWide<6>/*172:0*/ taiga_sim__DOT__cpu__DOT__issue;
        VlWide<5>/*141:0*/ taiga_sim__DOT__cpu__DOT__alu_inputs;
        VlWide<5>/*159:0*/ taiga_sim__DOT__cpu__DOT__ls_inputs;
        VlWide<5>/*159:0*/ taiga_sim__DOT__cpu__DOT__branch_inputs;
        VlWide<3>/*65:0*/ taiga_sim__DOT__cpu__DOT__mul_inputs;
        QData/*40:0*/ taiga_sim__DOT__cpu__DOT__gc_inputs;
        QData/*47:0*/ taiga_sim__DOT__cpu__DOT__csr_inputs;
        VlWide<13>/*399:0*/ taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet;
        VlWide<3>/*78:0*/ taiga_sim__DOT__cpu__DOT__decode;
        VlWide<4>/*114:0*/ taiga_sim__DOT__cpu__DOT__gc;
        QData/*35:0*/ taiga_sim__DOT__cpu__DOT__wb_snoop;
        VlWide<3>/*67:0*/ taiga_sim__DOT__cpu__DOT__fp_wb_snoop;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vlvbound_h8712ac2e__0;
        VlWide<5>/*148:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry;
        QData/*42:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry;
        QData/*43:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
        QData/*35:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__wb_snoop_r;
        VlWide<3>/*67:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_wb_snoop_r;
        QData/*47:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r;
        QData/*32:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle;
        QData/*32:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret;
        QData/*32:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_input_next;
        QData/*32:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_input_next;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__result;
        QData/*32:0*/ taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__rs1_r;
        QData/*32:0*/ taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__rs2_r;
        VlWide<3>/*81:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__fifo_inputs;
        VlWide<17>/*524:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed;
        VlWide<6>/*175:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed;
    };
    struct {
        VlWide<6>/*170:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed;
        VlWide<10>/*299:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs3;
        QData/*51:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_frac_pre_normalized;
        QData/*51:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_frac_pre_normalized;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped;
        QData/*52:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT____Vcellout__pre_normalize_rs1__frac_normalized;
        QData/*52:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT____Vcellout__pre_normalize_rs2__frac_normalized;
        VlWide<9>/*268:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs;
        QData/*52:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac;
        QData/*52:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac;
        VlWide<9>/*275:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs;
        VlWide<9>/*275:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r;
        VlWide<9>/*268:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs;
        VlWide<3>/*72:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb;
        QData/*52:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__mantissa_mul__DOT__rs1_r;
        QData/*52:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__mantissa_mul__DOT__rs2_r;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input;
        VlWide<3>/*83:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs;
        QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__normalized_radicand;
        QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__rad;
        QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__next_rad;
        QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__current_subtractend;
        QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__next_subtractend;
        QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__new_Q;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1;
        QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2;
        QData/*54:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__divisor_r;
        QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__new_PR;
        QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__PR;
        VlWide<3>/*68:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_r;
        VlWide<3>/*68:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr;
        VlWide<7>/*208:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet;
        VlWide<7>/*208:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r;
        VlWide<5>/*140:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet;
        VlWide<5>/*140:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r;
        VlWide<7>/*196:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet;
        VlWide<7>/*196:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r;
        QData/*53:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup;
        QData/*55:0*/ __Vdly__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__PR;
        VL_OUT(retire_ports_instruction[2],31,0);
        VL_OUT(retire_ports_pc[2],31,0);
        VL_OUT8(retire_ports_valid[2],0,0);
        VL_OUT8(taiga_events[26],0,0);
        VL_OUT8(fp_taiga_events[53],0,0);
        VL_OUT8(LargeSigTrace[32],0,0);
        VlUnpacked<CData/*4:0*/, 3> taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot;
        VlUnpacked<CData/*4:0*/, 64> taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table;
        VlUnpacked<QData/*42:0*/, 2> taiga_sim__DOT__l2_arb__DOT__requests_in;
        VlUnpacked<QData/*42:0*/, 2> taiga_sim__DOT__l2_arb__DOT__requests;
        VlUnpacked<IData/*31:0*/, 2> taiga_sim__DOT__l2_arb__DOT__input_data;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes;
        VlUnpacked<QData/*43:0*/, 16> taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<IData/*29:0*/, 2> taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation_address;
        VlUnpacked<CData/*6:0*/, 32> taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<IData/*31:0*/, 16> taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<QData/*34:0*/, 16> taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<QData/*42:0*/, 16> taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<QData/*42:0*/, 16> taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
    };
    struct {
        VlUnpacked<IData/*31:0*/, 16> taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<IData/*31:0*/, 16> taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<CData/*5:0*/, 2> taiga_sim__DOT__cpu__DOT__decode_phys_rs_addr;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__decode_rs_wb_group;
        VlUnpacked<CData/*5:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_decode_phys_rs_addr;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_decode_rs_wb_group;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__retire_ids;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__retire_port_valid;
        VlUnpacked<QData/*35:0*/, 2> taiga_sim__DOT__cpu__DOT__wb_packet;
        VlUnpacked<QData/*41:0*/, 2> taiga_sim__DOT__cpu__DOT__commit_packet;
        VlUnpacked<VlWide<3>/*67:0*/, 1> taiga_sim__DOT__cpu__DOT__fp_wb_packet;
        VlUnpacked<VlWide<3>/*73:0*/, 1> taiga_sim__DOT__cpu__DOT__fp_commit_packet;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellout__id_block__retire_port_valid;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellout__id_block__retire_ids;
        VlUnpacked<VlWide<3>/*73:0*/, 1> taiga_sim__DOT__cpu__DOT____Vcellout__id_block__fp_commit_packet;
        VlUnpacked<VlWide<3>/*67:0*/, 1> taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet;
        VlUnpacked<QData/*41:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet;
        VlUnpacked<QData/*35:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_rs_wb_group;
        VlUnpacked<CData/*5:0*/, 3> taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_phys_rs_addr;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_rs_wb_group;
        VlUnpacked<CData/*5:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_phys_rs_addr;
        VlUnpacked<QData/*41:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__commit;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_rs_wb_group;
        VlUnpacked<CData/*5:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr;
        VlUnpacked<VlWide<3>/*73:0*/, 1> taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__commit;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_rs_wb_group;
        VlUnpacked<CData/*5:0*/, 3> taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_port_valid;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_ids;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellinp__csr_unit_block__retire_ids;
        VlUnpacked<QData/*35:0*/, 2> taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet;
        VlUnpacked<VlWide<3>/*67:0*/, 1> taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet;
        VlUnpacked<IData/*31:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table;
        VlUnpacked<IData/*31:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__uses_rd_table;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__fetch_metadata_table;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr;
        VlUnpacked<CData/*2:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_is_post_issue;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_ready_to_retire;
        VlUnpacked<CData/*5:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT__commit_phys_addr;
        VlUnpacked<VlWide<3>/*73:0*/, 1> taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet;
        VlUnpacked<VlWide<3>/*67:0*/, 1> taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__retire_ids_next;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle;
        VlUnpacked<CData/*2:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr;
        VlUnpacked<VlUnpacked<CData/*0:0*/, 3>, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data;
        VlUnpacked<CData/*2:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data;
        VlUnpacked<CData/*2:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data;
        VlUnpacked<CData/*2:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data;
    };
    struct {
        VlUnpacked<CData/*2:0*/, 3> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__is_float_table;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_float_table;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__accu_fcsr_table;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_int_table;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__need_int_data_table;
        VlUnpacked<CData/*5:0*/, 1> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__commit_phys_addr;
        VlUnpacked<CData/*3:0*/, 8> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<IData/*31:0*/, 1> taiga_sim__DOT__cpu__DOT__fetch_block__DOT__unit_data_array;
        VlUnpacked<IData/*31:0*/, 4> taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_mux;
        VlUnpacked<CData/*4:0*/, 8> taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_table;
        VlUnpacked<IData/*22:0*/, 512> taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__0__KET____DOT__tag_bank__DOT__branch_ram;
        VlUnpacked<IData/*22:0*/, 512> taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__1__KET____DOT__tag_bank__DOT__branch_ram;
        VlUnpacked<IData/*31:0*/, 512> taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__0__KET____DOT__addr_table__DOT__branch_ram;
        VlUnpacked<IData/*31:0*/, 512> taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__1__KET____DOT__addr_table__DOT__branch_ram;
        VlUnpacked<IData/*31:0*/, 8> taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram;
        VlUnpacked<CData/*2:0*/, 8> taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<CData/*4:0*/, 3> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_addr;
        VlUnpacked<CData/*6:0*/, 3> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_data;
        VlUnpacked<CData/*6:0*/, 4> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux;
        VlUnpacked<CData/*4:0*/, 4> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index_mux;
        VlUnpacked<CData/*6:0*/, 3> taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out;
        VlUnpacked<CData/*4:0*/, 3> taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_ram__raddr;
        VlUnpacked<CData/*5:0*/, 32> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__lut_ram;
        VlUnpacked<IData/*17:0*/, 32> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<CData/*6:0*/, 32> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*4:0*/, 4> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr;
        VlUnpacked<CData/*6:0*/, 4> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data;
        VlUnpacked<CData/*6:0*/, 4> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux;
        VlUnpacked<CData/*4:0*/, 4> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index_mux;
        VlUnpacked<CData/*6:0*/, 4> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out;
        VlUnpacked<CData/*4:0*/, 4> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr;
        VlUnpacked<CData/*5:0*/, 32> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__lut_ram;
        VlUnpacked<IData/*17:0*/, 32> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<CData/*6:0*/, 32> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*2:0*/, 32> taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rd_to_id_table;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_rs_wb_group;
        VlUnpacked<CData/*5:0*/, 3> taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_phys_rs_addr;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_zero;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__hidden_bit;
        VlUnpacked<CData/*2:0*/, 32> taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rd_to_id_table;
        VlUnpacked<VlUnpacked<IData/*31:0*/, 2>, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_data_set;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse_r;
    };
    struct {
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use;
        VlUnpacked<CData/*5:0*/, 4> taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr;
        VlUnpacked<CData/*5:0*/, 3> taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_wb_group;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__bypass;
        VlUnpacked<IData/*31:0*/, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data;
        VlUnpacked<CData/*5:0*/, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr;
        VlUnpacked<IData/*31:0*/, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__1__KET____DOT__reg_group__data;
        VlUnpacked<CData/*5:0*/, 2> taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__1__KET____DOT__reg_group__read_addr;
        VlUnpacked<CData/*5:0*/, 4> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle;
        VlUnpacked<CData/*5:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr;
        VlUnpacked<VlUnpacked<CData/*0:0*/, 5>, 4> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data;
        VlUnpacked<CData/*5:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data;
        VlUnpacked<CData/*5:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data;
        VlUnpacked<CData/*5:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data;
        VlUnpacked<CData/*5:0*/, 5> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 64> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 64> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 64> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 64> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<IData/*31:0*/, 64> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank;
        VlUnpacked<IData/*31:0*/, 64> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__1__KET____DOT__reg_group__DOT__register_file_bank;
        VlUnpacked<VlUnpacked<QData/*63:0*/, 3>, 1> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_data_set;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse_r;
        VlUnpacked<CData/*0:0*/, 6> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use;
        VlUnpacked<CData/*5:0*/, 6> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr;
        VlUnpacked<CData/*5:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_wb_group;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__bypass;
        VlUnpacked<QData/*63:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data;
        VlUnpacked<CData/*5:0*/, 3> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr;
        VlUnpacked<CData/*5:0*/, 4> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle;
        VlUnpacked<CData/*5:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr;
        VlUnpacked<VlUnpacked<CData/*0:0*/, 7>, 4> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data;
        VlUnpacked<CData/*0:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use;
        VlUnpacked<CData/*0:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data;
        VlUnpacked<CData/*5:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data;
    };
    struct {
        VlUnpacked<CData/*5:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data;
        VlUnpacked<CData/*5:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data;
        VlUnpacked<CData/*5:0*/, 7> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 64> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 64> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 64> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id;
        VlUnpacked<CData/*0:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out;
        VlUnpacked<CData/*5:0*/, 8> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr;
        VlUnpacked<CData/*0:0*/, 64> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram;
        VlUnpacked<QData/*63:0*/, 64> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank;
        VlUnpacked<QData/*63:0*/, 2> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_port_valid;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_ids;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_retire_port_valid;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids;
        VlUnpacked<QData/*43:0*/, 8> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram;
        VlUnpacked<IData/*31:0*/, 4> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_issue;
        VlUnpacked<IData/*31:0*/, 4> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb;
        VlUnpacked<QData/*63:0*/, 4> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_issue;
        VlUnpacked<QData/*63:0*/, 4> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb;
        VlUnpacked<QData/*42:0*/, 4> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_attr;
        VlUnpacked<CData/*5:0*/, 2> taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack;
        VlUnpacked<IData/*17:0*/, 2> taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id;
        VlUnpacked<CData/*5:0*/, 2> taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done;
        VlUnpacked<VlUnpacked<IData/*31:0*/, 6>, 2> taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd;
        VlUnpacked<VlUnpacked<CData/*4:0*/, 6>, 2> taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel;
        VlUnpacked<CData/*1:0*/, 1> taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_ack;
        VlUnpacked<CData/*5:0*/, 1> taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_instruction_id;
        VlUnpacked<CData/*1:0*/, 1> taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done;
        VlUnpacked<VlUnpacked<QData/*63:0*/, 2>, 1> taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_rd;
        VlUnpacked<VlUnpacked<CData/*4:0*/, 2>, 1> taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_fflags;
        VlUnpacked<CData/*0:0*/, 1> taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__mulh;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__id;
        VlUnpacked<CData/*1:0*/, 8> taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz;
        VlUnpacked<CData/*1:0*/, 4> taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__upper_lower;
        VlUnpacked<CData/*1:0*/, 8> taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table;
        VlUnpacked<CData/*1:0*/, 8> taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz;
        VlUnpacked<CData/*1:0*/, 4> taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__upper_lower;
        VlUnpacked<CData/*1:0*/, 8> taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__new_request;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__id;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf;
    };
    struct {
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf_swapped;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN_swapped;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal_swapped;
        VlUnpacked<CData/*2:0*/, 5> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm;
        VlUnpacked<CData/*6:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__instruction;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_sign;
        VlUnpacked<SData/*10:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_expo;
        VlUnpacked<QData/*52:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_frac;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_sign;
        VlUnpacked<SData/*10:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_expo;
        VlUnpacked<SData/*10:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt;
        VlUnpacked<QData/*52:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_frac;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign;
        VlUnpacked<SData/*11:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__possible_subnormal;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__right_shift;
        VlUnpacked<QData/*53:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac;
        VlUnpacked<QData/*63:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__special_case_results;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case;
        VlUnpacked<QData/*51:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id;
        VlUnpacked<QData/*63:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit;
        VlUnpacked<CData/*3:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage;
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_sign;
        VlUnpacked<SData/*10:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo_overflow;
        VlUnpacked<QData/*53:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac;
        VlUnpacked<QData/*53:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__zero_result_sign;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract;
        VlUnpacked<CData/*0:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_sign;
        VlUnpacked<SData/*10:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo_overflow;
        VlUnpacked<QData/*54:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac;
        VlUnpacked<SData/*11:0*/, 3> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff;
        VlUnpacked<QData/*53:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned;
        VlUnpacked<VlWide<4>/*103:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs;
        VlUnpacked<VlWide<4>/*103:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN;
        VlUnpacked<CData/*0:0*/, 5> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done;
    };
    struct {
        VlUnpacked<CData/*2:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id;
        VlUnpacked<QData/*63:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__special_case_results;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs_sticky_bit;
        VlUnpacked<CData/*0:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage;
        VlUnpacked<QData/*52:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__result_frac;
        VlUnpacked<CData/*2:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__grs;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_sign;
        VlUnpacked<SData/*12:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate;
        VlUnpacked<QData/*63:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__special_case_results;
        VlUnpacked<CData/*0:0*/, 2> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case;
        VlUnpacked<CData/*1:0*/, 8> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz;
        VlUnpacked<CData/*1:0*/, 4> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__upper_lower;
        VlUnpacked<CData/*1:0*/, 8> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table;
        VlUnpacked<CData/*3:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack;
        VlUnpacked<SData/*11:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id;
        VlUnpacked<CData/*3:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done;
        VlUnpacked<VlUnpacked<QData/*63:0*/, 4>, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd;
        VlUnpacked<CData/*3:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry;
        VlUnpacked<CData/*3:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe;
        VlUnpacked<CData/*3:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden;
        VlUnpacked<CData/*3:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow;
        VlUnpacked<CData/*3:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift;
        VlUnpacked<CData/*3:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal;
        VlUnpacked<SData/*11:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm;
        VlUnpacked<VlUnpacked<CData/*4:0*/, 4>, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_fflags;
        VlUnpacked<QData/*43:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz;
        VlUnpacked<VlWide<13>/*415:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs;
        VlUnpacked<QData/*43:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt;
        VlUnpacked<CData/*1:0*/, 1> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel;
        VlUnpacked<CData/*4:0*/, 8> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__unit_fflags_table;
        VlUnpacked<CData/*4:0*/, 8> taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__fp_unit_fflags_table;
        VlUnpacked<CData/*0:0*/, 4> __Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage;
        VlUnpacked<CData/*0:0*/, 4> __Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage;
    };

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // PARAMETERS
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};

    // CONSTRUCTORS
    Vtaiga_sim___024root(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim___024root();
    VL_UNCOPYABLE(Vtaiga_sim___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
