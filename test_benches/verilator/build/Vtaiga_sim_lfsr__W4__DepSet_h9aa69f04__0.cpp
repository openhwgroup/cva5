// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim__Syms.h"
#include "Vtaiga_sim_lfsr__W4.h"

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP.taiga_sim__DOT__l2_to_mem__DOT__pop) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP.taiga_sim__DOT__l2_arb__DOT__advance) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP__taiga_sim__DOT__mem.wr_data_read) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_write_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_write_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo.push) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if ((0x10U & (IData)(vlSymsp->TOP.taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__inflight_count))) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_write_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_write_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP.ddr_axi_rvalid) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__0__KET__.pop) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP__taiga_sim__DOT__l2__BRA__0__KET__.request_push) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__1__KET__.pop) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0\n"); );
    // Init
    CData/*1:0*/ __PVT__feedback_input;
    // Body
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        vlSelf->value = 0U;
    }
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__0__KET__.pop) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP__taiga_sim__DOT__l2__BRA__0__KET__.wr_data_push) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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

VL_INLINE_OPT void Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_lfsr__W4___sequent__TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index__0\n"); );
    // Init
    CData/*3:0*/ __Vdly__value;
    // Body
    __Vdly__value = vlSelf->value;
    if ((1U & (IData)(vlSymsp->TOP.rst))) {
        __Vdly__value = 0U;
    } else if (vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__1__KET__.pop) {
        __Vdly__value = ((0xeU & ((IData)(vlSelf->value) 
                                  << 1U)) | (IData)(vlSelf->__PVT__feedback));
    }
    vlSelf->value = __Vdly__value;
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
