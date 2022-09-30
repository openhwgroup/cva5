// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim___024root.h"

QData Vtaiga_sim___024root___change_request_1(Vtaiga_sim___024root* vlSelf);

VL_INLINE_OPT QData Vtaiga_sim___024root___change_request(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___change_request\n"); );
    // Body
    return (Vtaiga_sim___024root___change_request_1(vlSelf));
}

VL_INLINE_OPT QData Vtaiga_sim___024root___change_request_1(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___change_request_1\n"); );
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    __req |= ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
               [0U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
               [0U])
         | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
            [1U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
            [1U])
         | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
            [2U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
            [2U])
         | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
            [3U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
            [3U])
         | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
            [0U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
            [0U])
         | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
            [1U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
            [1U])
         | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
            [2U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
            [2U])
         | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
            [3U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
            [3U]));
    VL_DEBUG_IF( if(__req && ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                               [0U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                               [0U]))) VL_DBG_MSGF("        CHANGE: /localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/fpu/fp_mul_madd_fused.sv:180\n"); );
    VL_DEBUG_IF( if(__req && ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                               [1U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                               [1U]))) VL_DBG_MSGF("        CHANGE: /localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/fpu/fp_mul_madd_fused.sv:180\n"); );
    VL_DEBUG_IF( if(__req && ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                               [2U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                               [2U]))) VL_DBG_MSGF("        CHANGE: /localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/fpu/fp_mul_madd_fused.sv:180\n"); );
    VL_DEBUG_IF( if(__req && ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                               [3U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                               [3U]))) VL_DBG_MSGF("        CHANGE: /localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/fpu/fp_mul_madd_fused.sv:180\n"); );
    VL_DEBUG_IF( if(__req && ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                               [0U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                               [0U]))) VL_DBG_MSGF("        CHANGE: /localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/fpu/fp_add_madd_fused.sv:248\n"); );
    VL_DEBUG_IF( if(__req && ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                               [1U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                               [1U]))) VL_DBG_MSGF("        CHANGE: /localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/fpu/fp_add_madd_fused.sv:248\n"); );
    VL_DEBUG_IF( if(__req && ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                               [2U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                               [2U]))) VL_DBG_MSGF("        CHANGE: /localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/fpu/fp_add_madd_fused.sv:248\n"); );
    VL_DEBUG_IF( if(__req && ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                               [3U] ^ vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                               [3U]))) VL_DBG_MSGF("        CHANGE: /localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/fpu/fp_add_madd_fused.sv:248\n"); );
    // Final
    vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
        [0U];
    vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
        [1U];
    vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
        [2U];
    vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
        [3U];
    vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
        [0U];
    vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
        [1U];
    vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
        [2U];
    vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
        [3U];
    return __req;
}

#ifdef VL_DEBUG
void Vtaiga_sim___024root___eval_debug_assertions(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((vlSelf->clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((vlSelf->rst & 0xfeU))) {
        Verilated::overWidthError("rst");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_arready & 0xfeU))) {
        Verilated::overWidthError("ddr_axi_arready");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_awready & 0xfeU))) {
        Verilated::overWidthError("ddr_axi_awready");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_bresp & 0xfcU))) {
        Verilated::overWidthError("ddr_axi_bresp");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_bvalid & 0xfeU))) {
        Verilated::overWidthError("ddr_axi_bvalid");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_rid & 0xc0U))) {
        Verilated::overWidthError("ddr_axi_rid");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_rlast & 0xfeU))) {
        Verilated::overWidthError("ddr_axi_rlast");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_rresp & 0xfcU))) {
        Verilated::overWidthError("ddr_axi_rresp");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_rvalid & 0xfeU))) {
        Verilated::overWidthError("ddr_axi_rvalid");}
    if (VL_UNLIKELY((vlSelf->ddr_axi_wready & 0xfeU))) {
        Verilated::overWidthError("ddr_axi_wready");}
    if (VL_UNLIKELY((vlSelf->addr & 0xc0000000U))) {
        Verilated::overWidthError("addr");}
    if (VL_UNLIKELY((vlSelf->be & 0xf0U))) {
        Verilated::overWidthError("be");}
    if (VL_UNLIKELY((vlSelf->rnw & 0xfeU))) {
        Verilated::overWidthError("rnw");}
    if (VL_UNLIKELY((vlSelf->is_amo & 0xfeU))) {
        Verilated::overWidthError("is_amo");}
    if (VL_UNLIKELY((vlSelf->amo_type_or_burst_size 
                     & 0xe0U))) {
        Verilated::overWidthError("amo_type_or_burst_size");}
    if (VL_UNLIKELY((vlSelf->sub_id & 0xfcU))) {
        Verilated::overWidthError("sub_id");}
    if (VL_UNLIKELY((vlSelf->request_push & 0xfeU))) {
        Verilated::overWidthError("request_push");}
    if (VL_UNLIKELY((vlSelf->inv_ack & 0xfeU))) {
        Verilated::overWidthError("inv_ack");}
    if (VL_UNLIKELY((vlSelf->wr_data_push & 0xfeU))) {
        Verilated::overWidthError("wr_data_push");}
    if (VL_UNLIKELY((vlSelf->rd_data_ack & 0xfeU))) {
        Verilated::overWidthError("rd_data_ack");}
}
#endif  // VL_DEBUG
