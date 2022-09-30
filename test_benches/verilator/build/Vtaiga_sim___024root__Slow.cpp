// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim__Syms.h"
#include "Vtaiga_sim___024root.h"

// Parameter definitions for Vtaiga_sim___024root
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS;
constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> Vtaiga_sim___024root::taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS;


void Vtaiga_sim___024root___ctor_var_reset(Vtaiga_sim___024root* vlSelf);

Vtaiga_sim___024root::Vtaiga_sim___024root(Vtaiga_sim__Syms* symsp, const char* name)
    : VerilatedModule{name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtaiga_sim___024root___ctor_var_reset(this);
}

void Vtaiga_sim___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

Vtaiga_sim___024root::~Vtaiga_sim___024root() {
}
