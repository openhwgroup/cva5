// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary model header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef VERILATED_VTAIGA_SIM_H_
#define VERILATED_VTAIGA_SIM_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;
class Vtaiga_sim___024root;
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


// This class is the main interface to the Verilated model
class Vtaiga_sim VL_NOT_FINAL : public VerilatedModel {
  private:
    // Symbol table holding complete model state (owned by this class)
    Vtaiga_sim__Syms* const vlSymsp;

  public:

    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(&clk,0,0);
    VL_IN8(&rst,0,0);
    VL_OUT8(&ddr_axi_arburst,1,0);
    VL_OUT8(&ddr_axi_arcache,3,0);
    VL_OUT8(&ddr_axi_arid,5,0);
    VL_OUT8(&ddr_axi_arlen,7,0);
    VL_OUT8(&ddr_axi_arlock,0,0);
    VL_OUT8(&ddr_axi_arprot,2,0);
    VL_OUT8(&ddr_axi_arqos,3,0);
    VL_IN8(&ddr_axi_arready,0,0);
    VL_OUT8(&ddr_axi_arregion,3,0);
    VL_OUT8(&ddr_axi_arsize,2,0);
    VL_OUT8(&ddr_axi_arvalid,0,0);
    VL_OUT8(&ddr_axi_awburst,1,0);
    VL_OUT8(&ddr_axi_awcache,3,0);
    VL_OUT8(&ddr_axi_awid,5,0);
    VL_OUT8(&ddr_axi_awlen,7,0);
    VL_OUT8(&ddr_axi_awlock,0,0);
    VL_OUT8(&ddr_axi_awprot,2,0);
    VL_OUT8(&ddr_axi_awqos,3,0);
    VL_IN8(&ddr_axi_awready,0,0);
    VL_OUT8(&ddr_axi_awregion,3,0);
    VL_OUT8(&ddr_axi_awsize,2,0);
    VL_OUT8(&ddr_axi_awvalid,0,0);
    VL_OUT8(&ddr_axi_bid,5,0);
    VL_OUT8(&ddr_axi_bready,0,0);
    VL_IN8(&ddr_axi_bresp,1,0);
    VL_IN8(&ddr_axi_bvalid,0,0);
    VL_IN8(&ddr_axi_rid,5,0);
    VL_IN8(&ddr_axi_rlast,0,0);
    VL_OUT8(&ddr_axi_rready,0,0);
    VL_IN8(&ddr_axi_rresp,1,0);
    VL_IN8(&ddr_axi_rvalid,0,0);
    VL_OUT8(&ddr_axi_wlast,0,0);
    VL_IN8(&ddr_axi_wready,0,0);
    VL_OUT8(&ddr_axi_wstrb,3,0);
    VL_OUT8(&ddr_axi_wvalid,0,0);
    VL_OUT8(&ddr_axi_wid,5,0);
    VL_IN8(&be,3,0);
    VL_IN8(&rnw,0,0);
    VL_IN8(&is_amo,0,0);
    VL_IN8(&amo_type_or_burst_size,4,0);
    VL_IN8(&sub_id,1,0);
    VL_IN8(&request_push,0,0);
    VL_OUT8(&request_full,0,0);
    VL_OUT8(&inv_valid,0,0);
    VL_IN8(&inv_ack,0,0);
    VL_OUT8(&con_result,0,0);
    VL_OUT8(&con_valid,0,0);
    VL_IN8(&wr_data_push,0,0);
    VL_OUT8(&data_full,0,0);
    VL_OUT8(&rd_sub_id,1,0);
    VL_OUT8(&rd_data_valid,0,0);
    VL_IN8(&rd_data_ack,0,0);
    VL_OUT8(&instruction_bram_en,0,0);
    VL_OUT8(&instruction_bram_be,3,0);
    VL_OUT8(&data_bram_we,1,0);
    VL_OUT8(&data_bram_en,0,0);
    VL_OUT8(&data_bram_be,3,0);
    VL_OUT8(&write_uart,0,0);
    VL_OUT8(&uart_byte,7,0);
    VL_OUT8(&store_queue_empty,0,0);
    VL_OUT8(&load_store_idle,0,0);
    VL_OUT8(&instruction_issued,0,0);
    VL_OUT(&ddr_axi_araddr,31,0);
    VL_OUT(&ddr_axi_awaddr,31,0);
    VL_IN(&ddr_axi_rdata,31,0);
    VL_OUT(&ddr_axi_wdata,31,0);
    VL_IN(&addr,29,0);
    VL_OUT(&inv_addr,31,2);
    VL_IN(&wr_data,31,0);
    VL_OUT(&rd_data,31,0);
    VL_OUT(&instruction_bram_addr,29,0);
    VL_OUT(&instruction_bram_data_in,31,0);
    VL_IN(&instruction_bram_data_out,31,0);
    VL_OUT(&data_bram_addr,28,0);
    VL_OUT(&NUM_RETIRE_PORTS,31,0);
    VL_OUT(&instruction_pc_dec,31,0);
    VL_OUT(&instruction_data_dec,31,0);
    VL_OUT64(&data_bram_data_in,63,0);
    VL_IN64(&data_bram_data_out,63,0);
    VL_IN64(&debug_instructions,63,0);
    VL_OUT((&retire_ports_instruction)[2],31,0);
    VL_OUT((&retire_ports_pc)[2],31,0);
    VL_OUT8((&retire_ports_valid)[2],0,0);
    VL_OUT8((&taiga_events)[26],0,0);
    VL_OUT8((&fp_taiga_events)[53],0,0);
    VL_OUT8((&LargeSigTrace)[32],0,0);

    // CELLS
    // Public to allow access to /* verilator public */ items.
    // Otherwise the application code can consider these internals.
    Vtaiga_sim_axi_interface* const __PVT__taiga_sim__DOT__m_axi;
    Vtaiga_sim_l2_requester_interface* const __PVT__taiga_sim__DOT__l2__BRA__1__KET__;
    Vtaiga_sim_l2_requester_interface* const __PVT__taiga_sim__DOT__l2__BRA__0__KET__;
    Vtaiga_sim_l2_memory_interface* const __PVT__taiga_sim__DOT__mem;
    Vtaiga_sim_l2_arbitration_interface* const __PVT__taiga_sim__DOT__l2_arb__DOT__arb;
    Vtaiga_sim_fifo_interface__D2b* const __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__1__KET__;
    Vtaiga_sim_fifo_interface__D2b* const __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D20* const __PVT__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__1__KET__;
    Vtaiga_sim_fifo_interface__D20* const __PVT__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D1e* const __PVT__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__1__KET__;
    Vtaiga_sim_fifo_interface__D1e* const __PVT__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D22* const __PVT__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__1__KET__;
    Vtaiga_sim_fifo_interface__D22* const __PVT__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D2c* const __PVT__taiga_sim__DOT__l2_arb__DOT__mem_addr_fifo;
    Vtaiga_sim_fifo_interface__D20* const __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo;
    Vtaiga_sim_fifo_interface__D7* const __PVT__taiga_sim__DOT__l2_arb__DOT__data_attributes;
    Vtaiga_sim_fifo_interface__D23* const __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata_fifo;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_read_index;
    Vtaiga_sim_lfsr__W4* const __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_write_index;
    Vtaiga_sim_branch_predictor_interface* const __PVT__taiga_sim__DOT__cpu__DOT__bp;
    Vtaiga_sim_ras_interface* const __PVT__taiga_sim__DOT__cpu__DOT__ras;
    Vtaiga_sim_register_file_issue_interface__pi1* const __PVT__taiga_sim__DOT__cpu__DOT__rf_issue;
    Vtaiga_sim_fp_register_file_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fp_rf_issue;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__10__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__9__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__8__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__7__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__6__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__5__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__4__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__3__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__2__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__1__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__0__KET__;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET__;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__3__KET__;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__2__KET__;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__1__KET__;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__0__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__1__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__0__KET__;
    Vtaiga_sim_tlb_interface* const __PVT__taiga_sim__DOT__cpu__DOT__itlb;
    Vtaiga_sim_tlb_interface* const __PVT__taiga_sim__DOT__cpu__DOT__dtlb;
    Vtaiga_sim_renamer_interface__N2* const __PVT__taiga_sim__DOT__cpu__DOT__decode_rename_interface;
    Vtaiga_sim_fp_renamer_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface;
    Vtaiga_sim_exception_interface* const __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__2__KET__;
    Vtaiga_sim_exception_interface* const __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__1__KET__;
    Vtaiga_sim_exception_interface* const __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__0__KET__;
    Vtaiga_sim_fifo_interface__D4* const __PVT__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__oldest_fp_issued_fifo;
    Vtaiga_sim_fetch_sub_unit_interface__pi5* const __PVT__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram;
    Vtaiga_sim_fifo_interface__D5* const __PVT__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo;
    Vtaiga_sim_fifo_interface__D3* const __PVT__taiga_sim__DOT__cpu__DOT__ras_block__DOT__ri_fifo;
    Vtaiga_sim_fifo_interface__D6* const __PVT__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list;
    Vtaiga_sim_fifo_interface__D12* const __PVT__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list;
    Vtaiga_sim_fifo_interface__D6* const __PVT__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list;
    Vtaiga_sim_fifo_interface__D12* const __PVT__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list;
    Vtaiga_sim_ls_sub_unit_interface__pi11* const __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bram;
    Vtaiga_sim_ls_sub_unit_interface__pi12* const __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bus;
    Vtaiga_sim_fifo_interface__Db* const __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes;
    Vtaiga_sim_load_store_queue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq;
    Vtaiga_sim_fifo_interface__D2c* const __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_fifo;
    Vtaiga_sim_unsigned_division_interface* const __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div;
    Vtaiga_sim_fifo_interface__D52* const __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo;
    Vtaiga_sim_fifo_interface__D20* const __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__wb_fifo;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__3__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__2__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__1__KET__;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__0__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__2__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__1__KET__;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__0__KET__;
    Vtaiga_sim_clz_tree* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz;
    Vtaiga_sim_clz_tree* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__mul_issue;
    Vtaiga_sim_fifo_interface__D110* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__add_issue;
    Vtaiga_sim_clz_tree* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz;
    Vtaiga_sim_clz_tree* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_issue;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_issue;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_wb;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb;
    Vtaiga_sim_fifo_interface__D54* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo;
    Vtaiga_sim_unsigned_sqrt_interface__D38* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt;
    Vtaiga_sim_fifo_interface__Db0* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo;
    Vtaiga_sim_unsigned_division_interface__pi16* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened;
    Vtaiga_sim_clz_tree* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__i2f_issue;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__minmax_issue;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__sign_inj_issue;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__i2f_wb;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__minmax_wb;
    Vtaiga_sim_fp_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__sign_inj_wb;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_issue;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_issue;
    Vtaiga_sim_unit_issue_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_issue;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_wb;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_wb;
    Vtaiga_sim_unit_writeback_interface* const __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_wb;

    // Root instance pointer to allow access to model internals,
    // including inlined /* verilator public_flat_* */ items.
    Vtaiga_sim___024root* const rootp;

    // CONSTRUCTORS
    /// Construct the model; called by application code
    /// If contextp is null, then the model will use the default global context
    /// If name is "", then makes a wrapper with a
    /// single model invisible with respect to DPI scope names.
    explicit Vtaiga_sim(VerilatedContext* contextp, const char* name = "TOP");
    explicit Vtaiga_sim(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    virtual ~Vtaiga_sim();
  private:
    VL_UNCOPYABLE(Vtaiga_sim);  ///< Copying not allowed

  public:
    // API METHODS
    /// Evaluate the model.  Application must call when inputs change.
    void eval() { eval_step(); }
    /// Evaluate when calling multiple units/models per time step.
    void eval_step();
    /// Evaluate at end of a timestep for tracing, when using eval_step().
    /// Application must call after all eval() and before time changes.
    void eval_end_step() {}
    /// Simulation complete, run final blocks.  Application must call on completion.
    void final();
    /// Retrieve name of this model instance (as passed to constructor).
    const char* name() const;

    // Abstract methods from VerilatedModel
    const char* hierName() const override final;
    const char* modelName() const override final;
    unsigned threads() const override final;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
