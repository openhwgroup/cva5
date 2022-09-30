// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim_fp_unit_writeback_interface.h"

VL_ATTR_COLD void Vtaiga_sim_fp_unit_writeback_interface___ctor_var_reset(Vtaiga_sim_fp_unit_writeback_interface* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_fp_unit_writeback_interface___ctor_var_reset\n"); );
    // Body
    vlSelf->ack = VL_RAND_RESET_I(1);
    vlSelf->id = VL_RAND_RESET_I(3);
    vlSelf->done = VL_RAND_RESET_I(1);
    vlSelf->rd = VL_RAND_RESET_Q(64);
    vlSelf->expo_overflow = VL_RAND_RESET_I(1);
    vlSelf->fflags = VL_RAND_RESET_I(5);
    vlSelf->rm = VL_RAND_RESET_I(3);
    vlSelf->carry = VL_RAND_RESET_I(1);
    vlSelf->safe = VL_RAND_RESET_I(1);
    vlSelf->hidden = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(104, vlSelf->grs);
    vlSelf->clz = VL_RAND_RESET_I(11);
    vlSelf->right_shift = VL_RAND_RESET_I(1);
    vlSelf->right_shift_amt = VL_RAND_RESET_I(11);
    vlSelf->subnormal = VL_RAND_RESET_I(1);
}
