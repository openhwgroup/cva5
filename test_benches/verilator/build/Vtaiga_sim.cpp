// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "Vtaiga_sim.h"
#include "Vtaiga_sim__Syms.h"

//============================================================
// Constructors

Vtaiga_sim::Vtaiga_sim(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new Vtaiga_sim__Syms(contextp(), _vcname__, this)}
    , clk{vlSymsp->TOP.clk}
    , rst{vlSymsp->TOP.rst}
    , ddr_axi_arburst{vlSymsp->TOP.ddr_axi_arburst}
    , ddr_axi_arcache{vlSymsp->TOP.ddr_axi_arcache}
    , ddr_axi_arid{vlSymsp->TOP.ddr_axi_arid}
    , ddr_axi_arlen{vlSymsp->TOP.ddr_axi_arlen}
    , ddr_axi_arlock{vlSymsp->TOP.ddr_axi_arlock}
    , ddr_axi_arprot{vlSymsp->TOP.ddr_axi_arprot}
    , ddr_axi_arqos{vlSymsp->TOP.ddr_axi_arqos}
    , ddr_axi_arready{vlSymsp->TOP.ddr_axi_arready}
    , ddr_axi_arregion{vlSymsp->TOP.ddr_axi_arregion}
    , ddr_axi_arsize{vlSymsp->TOP.ddr_axi_arsize}
    , ddr_axi_arvalid{vlSymsp->TOP.ddr_axi_arvalid}
    , ddr_axi_awburst{vlSymsp->TOP.ddr_axi_awburst}
    , ddr_axi_awcache{vlSymsp->TOP.ddr_axi_awcache}
    , ddr_axi_awid{vlSymsp->TOP.ddr_axi_awid}
    , ddr_axi_awlen{vlSymsp->TOP.ddr_axi_awlen}
    , ddr_axi_awlock{vlSymsp->TOP.ddr_axi_awlock}
    , ddr_axi_awprot{vlSymsp->TOP.ddr_axi_awprot}
    , ddr_axi_awqos{vlSymsp->TOP.ddr_axi_awqos}
    , ddr_axi_awready{vlSymsp->TOP.ddr_axi_awready}
    , ddr_axi_awregion{vlSymsp->TOP.ddr_axi_awregion}
    , ddr_axi_awsize{vlSymsp->TOP.ddr_axi_awsize}
    , ddr_axi_awvalid{vlSymsp->TOP.ddr_axi_awvalid}
    , ddr_axi_bid{vlSymsp->TOP.ddr_axi_bid}
    , ddr_axi_bready{vlSymsp->TOP.ddr_axi_bready}
    , ddr_axi_bresp{vlSymsp->TOP.ddr_axi_bresp}
    , ddr_axi_bvalid{vlSymsp->TOP.ddr_axi_bvalid}
    , ddr_axi_rid{vlSymsp->TOP.ddr_axi_rid}
    , ddr_axi_rlast{vlSymsp->TOP.ddr_axi_rlast}
    , ddr_axi_rready{vlSymsp->TOP.ddr_axi_rready}
    , ddr_axi_rresp{vlSymsp->TOP.ddr_axi_rresp}
    , ddr_axi_rvalid{vlSymsp->TOP.ddr_axi_rvalid}
    , ddr_axi_wlast{vlSymsp->TOP.ddr_axi_wlast}
    , ddr_axi_wready{vlSymsp->TOP.ddr_axi_wready}
    , ddr_axi_wstrb{vlSymsp->TOP.ddr_axi_wstrb}
    , ddr_axi_wvalid{vlSymsp->TOP.ddr_axi_wvalid}
    , ddr_axi_wid{vlSymsp->TOP.ddr_axi_wid}
    , be{vlSymsp->TOP.be}
    , rnw{vlSymsp->TOP.rnw}
    , is_amo{vlSymsp->TOP.is_amo}
    , amo_type_or_burst_size{vlSymsp->TOP.amo_type_or_burst_size}
    , sub_id{vlSymsp->TOP.sub_id}
    , request_push{vlSymsp->TOP.request_push}
    , request_full{vlSymsp->TOP.request_full}
    , inv_valid{vlSymsp->TOP.inv_valid}
    , inv_ack{vlSymsp->TOP.inv_ack}
    , con_result{vlSymsp->TOP.con_result}
    , con_valid{vlSymsp->TOP.con_valid}
    , wr_data_push{vlSymsp->TOP.wr_data_push}
    , data_full{vlSymsp->TOP.data_full}
    , rd_sub_id{vlSymsp->TOP.rd_sub_id}
    , rd_data_valid{vlSymsp->TOP.rd_data_valid}
    , rd_data_ack{vlSymsp->TOP.rd_data_ack}
    , instruction_bram_en{vlSymsp->TOP.instruction_bram_en}
    , instruction_bram_be{vlSymsp->TOP.instruction_bram_be}
    , data_bram_we{vlSymsp->TOP.data_bram_we}
    , data_bram_en{vlSymsp->TOP.data_bram_en}
    , data_bram_be{vlSymsp->TOP.data_bram_be}
    , write_uart{vlSymsp->TOP.write_uart}
    , uart_byte{vlSymsp->TOP.uart_byte}
    , store_queue_empty{vlSymsp->TOP.store_queue_empty}
    , load_store_idle{vlSymsp->TOP.load_store_idle}
    , instruction_issued{vlSymsp->TOP.instruction_issued}
    , ddr_axi_araddr{vlSymsp->TOP.ddr_axi_araddr}
    , ddr_axi_awaddr{vlSymsp->TOP.ddr_axi_awaddr}
    , ddr_axi_rdata{vlSymsp->TOP.ddr_axi_rdata}
    , ddr_axi_wdata{vlSymsp->TOP.ddr_axi_wdata}
    , addr{vlSymsp->TOP.addr}
    , inv_addr{vlSymsp->TOP.inv_addr}
    , wr_data{vlSymsp->TOP.wr_data}
    , rd_data{vlSymsp->TOP.rd_data}
    , instruction_bram_addr{vlSymsp->TOP.instruction_bram_addr}
    , instruction_bram_data_in{vlSymsp->TOP.instruction_bram_data_in}
    , instruction_bram_data_out{vlSymsp->TOP.instruction_bram_data_out}
    , data_bram_addr{vlSymsp->TOP.data_bram_addr}
    , NUM_RETIRE_PORTS{vlSymsp->TOP.NUM_RETIRE_PORTS}
    , instruction_pc_dec{vlSymsp->TOP.instruction_pc_dec}
    , instruction_data_dec{vlSymsp->TOP.instruction_data_dec}
    , data_bram_data_in{vlSymsp->TOP.data_bram_data_in}
    , data_bram_data_out{vlSymsp->TOP.data_bram_data_out}
    , debug_instructions{vlSymsp->TOP.debug_instructions}
    , retire_ports_instruction{vlSymsp->TOP.retire_ports_instruction}
    , retire_ports_pc{vlSymsp->TOP.retire_ports_pc}
    , retire_ports_valid{vlSymsp->TOP.retire_ports_valid}
    , taiga_events{vlSymsp->TOP.taiga_events}
    , fp_taiga_events{vlSymsp->TOP.fp_taiga_events}
    , LargeSigTrace{vlSymsp->TOP.LargeSigTrace}
    , __PVT__taiga_sim__DOT__m_axi{vlSymsp->TOP.__PVT__taiga_sim__DOT__m_axi}
    , __PVT__taiga_sim__DOT__l2__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__l2__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__mem{vlSymsp->TOP.__PVT__taiga_sim__DOT__mem}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__arb{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__arb}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__mem_addr_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__mem_addr_fifo}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__data_attributes{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__data_attributes}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata_fifo}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_read_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_read_index}
    , __PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_write_index{vlSymsp->TOP.__PVT__taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__lfsr_write_index}
    , __PVT__taiga_sim__DOT__cpu__DOT__bp{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__bp}
    , __PVT__taiga_sim__DOT__cpu__DOT__ras{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__ras}
    , __PVT__taiga_sim__DOT__cpu__DOT__rf_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__rf_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fp_rf_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fp_rf_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__10__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__10__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__9__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__9__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__8__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__8__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__7__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__7__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__6__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__6__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__5__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__5__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__4__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__4__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__3__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__3__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__2__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__2__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__3__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__3__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__2__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__2__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__itlb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__itlb}
    , __PVT__taiga_sim__DOT__cpu__DOT__dtlb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__dtlb}
    , __PVT__taiga_sim__DOT__cpu__DOT__decode_rename_interface{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__decode_rename_interface}
    , __PVT__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface}
    , __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__2__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__2__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__exception__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__oldest_fp_issued_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__oldest_fp_issued_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram}
    , __PVT__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__ras_block__DOT__ri_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__ras_block__DOT__ri_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list}
    , __PVT__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list}
    , __PVT__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list}
    , __PVT__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list}
    , __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bram{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bram}
    , __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bus{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bus}
    , __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes}
    , __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq}
    , __PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div}
    , __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__wb_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__wb_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__3__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__3__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__2__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__2__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__2__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__2__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__1__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__1__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__0__KET__{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__0__KET__}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__mul_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__mul_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__add_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__add_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_wb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_wb}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__i2f_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__i2f_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__minmax_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__minmax_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__sign_inj_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__sign_inj_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__i2f_wb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__i2f_wb}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__minmax_wb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__minmax_wb}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__sign_inj_wb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__sign_inj_wb}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_issue{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_issue}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_wb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_wb}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_wb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_wb}
    , __PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_wb{vlSymsp->TOP.__PVT__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_wb}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

Vtaiga_sim::Vtaiga_sim(const char* _vcname__)
    : Vtaiga_sim(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

Vtaiga_sim::~Vtaiga_sim() {
    delete vlSymsp;
}

//============================================================
// Evaluation loop

void Vtaiga_sim___024root___eval_initial(Vtaiga_sim___024root* vlSelf);
void Vtaiga_sim___024root___eval_settle(Vtaiga_sim___024root* vlSelf);
void Vtaiga_sim___024root___eval(Vtaiga_sim___024root* vlSelf);
QData Vtaiga_sim___024root___change_request(Vtaiga_sim___024root* vlSelf);
#ifdef VL_DEBUG
void Vtaiga_sim___024root___eval_debug_assertions(Vtaiga_sim___024root* vlSelf);
#endif  // VL_DEBUG
void Vtaiga_sim___024root___final(Vtaiga_sim___024root* vlSelf);

static void _eval_initial_loop(Vtaiga_sim__Syms* __restrict vlSymsp) {
    vlSymsp->__Vm_didInit = true;
    Vtaiga_sim___024root___eval_initial(&(vlSymsp->TOP));
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial loop\n"););
        Vtaiga_sim___024root___eval_settle(&(vlSymsp->TOP));
        Vtaiga_sim___024root___eval(&(vlSymsp->TOP));
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = Vtaiga_sim___024root___change_request(&(vlSymsp->TOP));
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("/localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../test_benches/verilator/taiga_sim.sv", 23, "",
                "Verilated model didn't DC converge\n"
                "- See https://verilator.org/warn/DIDNOTCONVERGE");
        } else {
            __Vchange = Vtaiga_sim___024root___change_request(&(vlSymsp->TOP));
        }
    } while (VL_UNLIKELY(__Vchange));
}

void Vtaiga_sim::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vtaiga_sim::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    Vtaiga_sim___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    // Initialize
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) _eval_initial_loop(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Clock loop\n"););
        Vtaiga_sim___024root___eval(&(vlSymsp->TOP));
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = Vtaiga_sim___024root___change_request(&(vlSymsp->TOP));
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("/localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../test_benches/verilator/taiga_sim.sv", 23, "",
                "Verilated model didn't converge\n"
                "- See https://verilator.org/warn/DIDNOTCONVERGE");
        } else {
            __Vchange = Vtaiga_sim___024root___change_request(&(vlSymsp->TOP));
        }
    } while (VL_UNLIKELY(__Vchange));
    // Evaluate cleanup
}

//============================================================
// Utilities

const char* Vtaiga_sim::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

VL_ATTR_COLD void Vtaiga_sim::final() {
    Vtaiga_sim___024root___final(&(vlSymsp->TOP));
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* Vtaiga_sim::hierName() const { return vlSymsp->name(); }
const char* Vtaiga_sim::modelName() const { return "Vtaiga_sim"; }
unsigned Vtaiga_sim::threads() const { return 1; }
