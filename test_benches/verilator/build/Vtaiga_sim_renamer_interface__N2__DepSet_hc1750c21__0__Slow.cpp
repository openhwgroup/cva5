// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim_renamer_interface__N2.h"

VL_ATTR_COLD void Vtaiga_sim_renamer_interface__N2___ctor_var_reset(Vtaiga_sim_renamer_interface__N2* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtaiga_sim_renamer_interface__N2___ctor_var_reset\n"); );
    // Body
    vlSelf->phys_rs_addr = VL_RAND_RESET_I(12);
    vlSelf->phys_rd_addr = VL_RAND_RESET_I(6);
    vlSelf->rs_wb_group = VL_RAND_RESET_I(2);
}
