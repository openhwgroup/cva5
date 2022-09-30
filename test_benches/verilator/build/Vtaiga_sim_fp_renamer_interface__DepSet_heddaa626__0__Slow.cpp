// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim_fp_renamer_interface.h"

VL_ATTR_COLD void Vtaiga_sim_fp_renamer_interface___ctor_var_reset(Vtaiga_sim_fp_renamer_interface* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtaiga_sim_fp_renamer_interface___ctor_var_reset\n"); );
    // Body
    vlSelf->phys_rs_addr = VL_RAND_RESET_I(18);
    vlSelf->rs_wb_group = VL_RAND_RESET_I(3);
}
