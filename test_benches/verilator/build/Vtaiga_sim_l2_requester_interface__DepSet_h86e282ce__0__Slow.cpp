// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim_l2_requester_interface.h"

VL_ATTR_COLD void Vtaiga_sim_l2_requester_interface___ctor_var_reset(Vtaiga_sim_l2_requester_interface* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtaiga_sim_l2_requester_interface___ctor_var_reset\n"); );
    // Body
    vlSelf->addr = VL_RAND_RESET_I(30);
    vlSelf->be = VL_RAND_RESET_I(4);
    vlSelf->rnw = VL_RAND_RESET_I(1);
    vlSelf->is_amo = VL_RAND_RESET_I(1);
    vlSelf->amo_type_or_burst_size = VL_RAND_RESET_I(5);
    vlSelf->sub_id = VL_RAND_RESET_I(2);
    vlSelf->request_push = VL_RAND_RESET_I(1);
    vlSelf->inv_ack = VL_RAND_RESET_I(1);
    vlSelf->wr_data = VL_RAND_RESET_I(32);
    vlSelf->wr_data_push = VL_RAND_RESET_I(1);
    vlSelf->rd_data_ack = VL_RAND_RESET_I(1);
}
