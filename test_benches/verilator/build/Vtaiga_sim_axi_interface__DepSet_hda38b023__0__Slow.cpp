// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim_axi_interface.h"

VL_ATTR_COLD void Vtaiga_sim_axi_interface___ctor_var_reset(Vtaiga_sim_axi_interface* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtaiga_sim_axi_interface___ctor_var_reset\n"); );
    // Body
    vlSelf->arready = VL_RAND_RESET_I(1);
    vlSelf->rvalid = VL_RAND_RESET_I(1);
    vlSelf->rdata = VL_RAND_RESET_I(32);
    vlSelf->awready = VL_RAND_RESET_I(1);
    vlSelf->awaddr = VL_RAND_RESET_I(32);
    vlSelf->wready = VL_RAND_RESET_I(1);
    vlSelf->wdata = VL_RAND_RESET_I(32);
    vlSelf->bvalid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__rvalid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__arready = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__wready = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__awready = VL_RAND_RESET_I(1);
}
