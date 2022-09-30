// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim_unit_writeback_interface.h"

VL_ATTR_COLD void Vtaiga_sim_unit_writeback_interface___ctor_var_reset(Vtaiga_sim_unit_writeback_interface* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                Vtaiga_sim_unit_writeback_interface___ctor_var_reset\n"); );
    // Body
    vlSelf->id = VL_RAND_RESET_I(3);
    vlSelf->done = VL_RAND_RESET_I(1);
    vlSelf->fflags = VL_RAND_RESET_I(5);
}
