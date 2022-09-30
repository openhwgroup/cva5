// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim_lfsr__W4.h"

VL_ATTR_COLD void Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Body
    vlSelf->value = 0U;
}

VL_ATTR_COLD void Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Body
    vlSelf->__PVT__feedback_input = ((2U & (IData)(vlSelf->__PVT__feedback_input)) 
                                     | (1U & ((IData)(vlSelf->value) 
                                              >> (3U 
                                                  & (vlSelf->__PVT__TAPS
                                                     [1U]
                                                     [1U] 
                                                     - (IData)(1U))))));
    vlSelf->__PVT__feedback_input = ((1U & (IData)(vlSelf->__PVT__feedback_input)) 
                                     | (2U & (((IData)(vlSelf->value) 
                                               >> (3U 
                                                   & (vlSelf->__PVT__TAPS
                                                      [1U]
                                                      [2U] 
                                                      - (IData)(1U)))) 
                                              << 1U)));
    vlSelf->__PVT__feedback = (1U & ((~ VL_REDXOR_2(vlSelf->__PVT__feedback_input)) 
                                     ^ (0U != (7U & (IData)(vlSelf->value)))));
}

VL_ATTR_COLD void Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0\n"); );
    // Init
    CData/*1:0*/ __PVT__feedback_input;
    // Body
    __PVT__feedback_input = ((2U & (IData)(__PVT__feedback_input)) 
                             | (1U & ((IData)(vlSelf->value) 
                                      >> (3U & (vlSelf->__PVT__TAPS
                                                [1U]
                                                [1U] 
                                                - (IData)(1U))))));
    __PVT__feedback_input = ((1U & (IData)(__PVT__feedback_input)) 
                             | (2U & (((IData)(vlSelf->value) 
                                       >> (3U & (vlSelf->__PVT__TAPS
                                                 [1U]
                                                 [2U] 
                                                 - (IData)(1U)))) 
                                      << 1U)));
}

VL_ATTR_COLD void Vtaiga_sim_lfsr__W4___ctor_var_reset(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___ctor_var_reset\n"); );
    // Body
    vlSelf->clk = VL_RAND_RESET_I(1);
    vlSelf->rst = VL_RAND_RESET_I(1);
    vlSelf->en = VL_RAND_RESET_I(1);
    vlSelf->value = VL_RAND_RESET_I(4);
    vlSelf->__PVT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->__PVT__feedback = VL_RAND_RESET_I(1);
}
