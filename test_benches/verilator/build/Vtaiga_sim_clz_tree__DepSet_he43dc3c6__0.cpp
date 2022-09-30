// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim__Syms.h"
#include "Vtaiga_sim_clz_tree.h"

VL_INLINE_OPT void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz__0\n"); );
    // Init
    IData/*19:0*/ __PVT__compressed_5bit_vector;
    SData/*11:0*/ __PVT__compressed_6bit_vector;
    // Body
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffffcULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | (IData)((IData)(
                                                      ((0U 
                                                        == 
                                                        (3U 
                                                         & (IData)(vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac)))
                                                        ? 2U
                                                        : 
                                                       ((1U 
                                                         == 
                                                         (3U 
                                                          & (IData)(vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac)))
                                                         ? 1U
                                                         : 0U)))));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffff3ULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 2U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 2U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 2U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffffcfULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 4U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 4U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 4U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffff3fULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 6U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 6U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 6U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffcffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 8U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 8U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 8U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffff3ffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0xaU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0xaU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xaU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffcfffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0xcU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0xcU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xcU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffff3fffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0xeU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0xeU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xeU));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffcffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x10U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x10U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x10U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffff3ffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x12U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x12U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x12U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffcfffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x14U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x14U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x14U));
    vlSelf->__PVT__encoded_input = ((0xffffffffff3fffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x16U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x16U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x16U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffcffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x18U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x18U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x18U));
    vlSelf->__PVT__encoded_input = ((0xfffffffff3ffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x1aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x1aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1aU));
    vlSelf->__PVT__encoded_input = ((0xffffffffcfffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x1cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x1cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1cU));
    vlSelf->__PVT__encoded_input = ((0xffffffff3fffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x1eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x1eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1eU));
    vlSelf->__PVT__encoded_input = ((0xfffffffcffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x20U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x20U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x20U));
    vlSelf->__PVT__encoded_input = ((0xfffffff3ffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x22U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x22U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x22U));
    vlSelf->__PVT__encoded_input = ((0xffffffcfffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x24U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x24U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x24U));
    vlSelf->__PVT__encoded_input = ((0xffffff3fffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x26U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x26U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x26U));
    vlSelf->__PVT__encoded_input = ((0xfffffcffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x28U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x28U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x28U));
    vlSelf->__PVT__encoded_input = ((0xfffff3ffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x2aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x2aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2aU));
    vlSelf->__PVT__encoded_input = ((0xffffcfffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x2cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x2cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2cU));
    vlSelf->__PVT__encoded_input = ((0xffff3fffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x2eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x2eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2eU));
    vlSelf->__PVT__encoded_input = ((0xfffcffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x30U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x30U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x30U));
    vlSelf->__PVT__encoded_input = ((0xfff3ffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x32U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x32U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x32U));
    vlSelf->__PVT__encoded_input = ((0xffcfffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x34U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x34U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x34U));
    vlSelf->__PVT__encoded_input = ((0xff3fffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x36U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x36U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x36U));
    vlSelf->__PVT__encoded_input = ((0xfcffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x38U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x38U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x38U));
    vlSelf->__PVT__encoded_input = ((0xf3ffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x3aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x3aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3aU));
    vlSelf->__PVT__encoded_input = ((0xcfffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x3cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x3cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3cU));
    vlSelf->__PVT__encoded_input = ((0x3fffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                     >> 0x3eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                                                      >> 0x3eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3eU));
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 3U)))) {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 1U))) << 1U)) 
                  | (1U & (IData)(vlSelf->__PVT__encoded_input))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 2U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 7U)))) {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 5U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 4U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 6U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 9U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 8U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xaU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xfU)))) {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000ULL == (0xa000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0xdU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000ULL == (0xa000ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xeU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x13U)))) {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000ULL == (0xa0000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x11U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x10U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000ULL == (0xa0000ULL 
                                        & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x12U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000ULL == (0xa00000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x15U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x14U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000ULL == (0xa00000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x16U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000ULL == (0xa000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x19U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000ULL == (0xa000000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000ULL == (0xa0000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x1dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x1cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000ULL == (0xa0000000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000ULL == (0xa00000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x21U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x20U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000ULL == (0xa00000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x22U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x27U)))) {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000ULL == (0xa000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x25U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000ULL == (0xa000000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x26U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x29U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x28U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x2dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x2cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x33U)))) {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x31U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x30U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x32U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x37U)))) {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x35U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x34U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x36U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000000ULL == 
                           (0xa00000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x39U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x38U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000000ULL == (0xa00000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000000ULL == 
                           (0xa000000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x3dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x3cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000000ULL == (0xa000000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3eU))));
    }
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffff000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | (IData)((IData)(
                                                               (((IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2) 
                                                                 << 9U) 
                                                                | (((IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2) 
                                                                    << 6U) 
                                                                   | (((IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2) 
                                                                       << 3U) 
                                                                      | (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)))))));
    vlSelf->__PVT__compressed_3bit_vector = ((0xffffff000fffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0xcU));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfff000ffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x18U));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x24U));
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 5U)))) {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 2U))) << 2U)) 
                  | (3U & (IData)(vlSelf->__PVT__compressed_3bit_vector))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 3U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 8U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 6U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 9U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x11U)))) {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000ULL == (0x24000ULL 
                                          & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0xeU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000ULL == (0x24000ULL 
                                        & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0xfU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000ULL == (0x900000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x14U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x12U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000ULL == (0x900000ULL 
                                         & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x15U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x1dU)))) {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000ULL == (0x24000000ULL 
                                             & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x1aU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000ULL == (0x24000000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x1bU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000ULL == (0x900000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x20U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x1eU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000ULL == (0x900000000ULL 
                                            & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x21U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x29U)))) {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000000ULL == (0x24000000000ULL 
                                                & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x26U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000000ULL == (0x24000000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x27U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000000ULL == (0x900000000000ULL 
                                                 & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x2cU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x2aU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000000ULL == (0x900000000000ULL 
                                               & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x2dU))));
    }
    vlSelf->__PVT__compressed_4bit_vector = ((0xffff0000U 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0xcU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 8U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 4U) 
                                                      | (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)))));
    vlSelf->__PVT__compressed_4bit_vector = ((0xffffU 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0x1cU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 0x18U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 0x14U) 
                                                      | ((IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2) 
                                                         << 0x10U)))));
    if ((0x80U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 3U)) << 3U)) | (7U 
                                                & vlSelf->__PVT__compressed_4bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 4U)));
    }
    if ((0x8000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0xbU)) << 3U)) | (7U 
                                                  & (vlSelf->__PVT__compressed_4bit_vector 
                                                     >> 8U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0xcU)));
    }
    if ((0x800000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x880000U == (0x880000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x13U)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x10U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x880000U == (0x880000U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x14U)));
    }
    if ((vlSelf->__PVT__compressed_4bit_vector >> 0x1fU)) {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88000000U == (0x88000000U 
                                           & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x1bU)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x18U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88000000U == (0x88000000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x1cU)));
    }
    __PVT__compressed_5bit_vector = (((IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2) 
                                      << 0xfU) | (((IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2) 
                                                   << 0xaU) 
                                                  | (((IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2) 
                                                      << 5U) 
                                                     | (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2))));
    if ((0x200U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 4U)) << 4U)) | (0xfU 
                                                   & __PVT__compressed_5bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 5U)));
    }
    if ((0x80000U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 0xeU)) << 4U)) | 
                  (0xfU & (__PVT__compressed_5bit_vector 
                           >> 0xaU))));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 0xfU)));
    }
    __PVT__compressed_6bit_vector = (((IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2) 
                                      << 6U) | (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2));
    if ((0x800U & (IData)(__PVT__compressed_6bit_vector))) {
        vlSelf->__PVT__clz_plus1 = ((0x3fU & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((IData)((0x820U 
                                                == 
                                                (0x820U 
                                                 & (IData)(__PVT__compressed_6bit_vector)))) 
                                       << 6U));
        vlSelf->__PVT__clz_plus1 = ((0x40U & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((0x20U & ((~ 
                                                  ((IData)(__PVT__compressed_6bit_vector) 
                                                   >> 5U)) 
                                                 << 5U)) 
                                       | (0x1fU & (IData)(__PVT__compressed_6bit_vector))));
    } else {
        vlSelf->__PVT__clz_plus1 = (((IData)((0x820U 
                                              == (0x820U 
                                                  & (IData)(__PVT__compressed_6bit_vector)))) 
                                     << 6U) | (0x1fU 
                                               & ((IData)(__PVT__compressed_6bit_vector) 
                                                  >> 6U)));
    }
}

VL_INLINE_OPT void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz__0\n"); );
    // Init
    IData/*19:0*/ __PVT__compressed_5bit_vector;
    SData/*11:0*/ __PVT__compressed_6bit_vector;
    // Body
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffffcULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | (IData)((IData)(
                                                      ((0U 
                                                        == 
                                                        (3U 
                                                         & (IData)(vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac)))
                                                        ? 2U
                                                        : 
                                                       ((1U 
                                                         == 
                                                         (3U 
                                                          & (IData)(vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac)))
                                                         ? 1U
                                                         : 0U)))));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffff3ULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 2U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 2U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 2U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffffcfULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 4U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 4U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 4U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffff3fULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 6U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 6U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 6U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffcffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 8U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 8U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 8U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffff3ffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0xaU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0xaU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xaU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffcfffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0xcU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0xcU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xcU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffff3fffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0xeU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0xeU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xeU));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffcffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x10U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x10U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x10U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffff3ffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x12U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x12U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x12U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffcfffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x14U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x14U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x14U));
    vlSelf->__PVT__encoded_input = ((0xffffffffff3fffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x16U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x16U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x16U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffcffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x18U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x18U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x18U));
    vlSelf->__PVT__encoded_input = ((0xfffffffff3ffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x1aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x1aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1aU));
    vlSelf->__PVT__encoded_input = ((0xffffffffcfffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x1cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x1cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1cU));
    vlSelf->__PVT__encoded_input = ((0xffffffff3fffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x1eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x1eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1eU));
    vlSelf->__PVT__encoded_input = ((0xfffffffcffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x20U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x20U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x20U));
    vlSelf->__PVT__encoded_input = ((0xfffffff3ffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x22U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x22U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x22U));
    vlSelf->__PVT__encoded_input = ((0xffffffcfffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x24U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x24U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x24U));
    vlSelf->__PVT__encoded_input = ((0xffffff3fffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x26U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x26U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x26U));
    vlSelf->__PVT__encoded_input = ((0xfffffcffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x28U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x28U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x28U));
    vlSelf->__PVT__encoded_input = ((0xfffff3ffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x2aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x2aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2aU));
    vlSelf->__PVT__encoded_input = ((0xffffcfffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x2cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x2cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2cU));
    vlSelf->__PVT__encoded_input = ((0xffff3fffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x2eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x2eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2eU));
    vlSelf->__PVT__encoded_input = ((0xfffcffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x30U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x30U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x30U));
    vlSelf->__PVT__encoded_input = ((0xfff3ffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x32U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x32U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x32U));
    vlSelf->__PVT__encoded_input = ((0xffcfffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x34U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x34U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x34U));
    vlSelf->__PVT__encoded_input = ((0xff3fffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x36U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x36U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x36U));
    vlSelf->__PVT__encoded_input = ((0xfcffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x38U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x38U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x38U));
    vlSelf->__PVT__encoded_input = ((0xf3ffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x3aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x3aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3aU));
    vlSelf->__PVT__encoded_input = ((0xcfffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x3cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x3cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3cU));
    vlSelf->__PVT__encoded_input = ((0x3fffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                     >> 0x3eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                                                      >> 0x3eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3eU));
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 3U)))) {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 1U))) << 1U)) 
                  | (1U & (IData)(vlSelf->__PVT__encoded_input))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 2U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 7U)))) {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 5U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 4U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 6U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 9U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 8U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xaU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xfU)))) {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000ULL == (0xa000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0xdU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000ULL == (0xa000ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xeU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x13U)))) {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000ULL == (0xa0000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x11U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x10U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000ULL == (0xa0000ULL 
                                        & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x12U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000ULL == (0xa00000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x15U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x14U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000ULL == (0xa00000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x16U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000ULL == (0xa000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x19U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000ULL == (0xa000000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000ULL == (0xa0000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x1dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x1cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000ULL == (0xa0000000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000ULL == (0xa00000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x21U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x20U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000ULL == (0xa00000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x22U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x27U)))) {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000ULL == (0xa000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x25U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000ULL == (0xa000000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x26U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x29U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x28U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x2dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x2cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x33U)))) {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x31U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x30U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x32U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x37U)))) {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x35U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x34U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x36U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000000ULL == 
                           (0xa00000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x39U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x38U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000000ULL == (0xa00000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000000ULL == 
                           (0xa000000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x3dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x3cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000000ULL == (0xa000000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3eU))));
    }
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffff000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | (IData)((IData)(
                                                               (((IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2) 
                                                                 << 9U) 
                                                                | (((IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2) 
                                                                    << 6U) 
                                                                   | (((IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2) 
                                                                       << 3U) 
                                                                      | (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)))))));
    vlSelf->__PVT__compressed_3bit_vector = ((0xffffff000fffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0xcU));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfff000ffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x18U));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x24U));
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 5U)))) {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 2U))) << 2U)) 
                  | (3U & (IData)(vlSelf->__PVT__compressed_3bit_vector))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 3U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 8U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 6U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 9U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x11U)))) {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000ULL == (0x24000ULL 
                                          & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0xeU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000ULL == (0x24000ULL 
                                        & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0xfU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000ULL == (0x900000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x14U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x12U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000ULL == (0x900000ULL 
                                         & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x15U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x1dU)))) {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000ULL == (0x24000000ULL 
                                             & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x1aU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000ULL == (0x24000000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x1bU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000ULL == (0x900000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x20U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x1eU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000ULL == (0x900000000ULL 
                                            & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x21U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x29U)))) {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000000ULL == (0x24000000000ULL 
                                                & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x26U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000000ULL == (0x24000000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x27U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000000ULL == (0x900000000000ULL 
                                                 & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x2cU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x2aU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000000ULL == (0x900000000000ULL 
                                               & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x2dU))));
    }
    vlSelf->__PVT__compressed_4bit_vector = ((0xffff0000U 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0xcU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 8U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 4U) 
                                                      | (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)))));
    vlSelf->__PVT__compressed_4bit_vector = ((0xffffU 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0x1cU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 0x18U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 0x14U) 
                                                      | ((IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2) 
                                                         << 0x10U)))));
    if ((0x80U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 3U)) << 3U)) | (7U 
                                                & vlSelf->__PVT__compressed_4bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 4U)));
    }
    if ((0x8000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0xbU)) << 3U)) | (7U 
                                                  & (vlSelf->__PVT__compressed_4bit_vector 
                                                     >> 8U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0xcU)));
    }
    if ((0x800000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x880000U == (0x880000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x13U)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x10U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x880000U == (0x880000U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x14U)));
    }
    if ((vlSelf->__PVT__compressed_4bit_vector >> 0x1fU)) {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88000000U == (0x88000000U 
                                           & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x1bU)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x18U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88000000U == (0x88000000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x1cU)));
    }
    __PVT__compressed_5bit_vector = (((IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2) 
                                      << 0xfU) | (((IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2) 
                                                   << 0xaU) 
                                                  | (((IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2) 
                                                      << 5U) 
                                                     | (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2))));
    if ((0x200U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 4U)) << 4U)) | (0xfU 
                                                   & __PVT__compressed_5bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 5U)));
    }
    if ((0x80000U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 0xeU)) << 4U)) | 
                  (0xfU & (__PVT__compressed_5bit_vector 
                           >> 0xaU))));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 0xfU)));
    }
    __PVT__compressed_6bit_vector = (((IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2) 
                                      << 6U) | (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2));
    if ((0x800U & (IData)(__PVT__compressed_6bit_vector))) {
        vlSelf->__PVT__clz_plus1 = ((0x3fU & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((IData)((0x820U 
                                                == 
                                                (0x820U 
                                                 & (IData)(__PVT__compressed_6bit_vector)))) 
                                       << 6U));
        vlSelf->__PVT__clz_plus1 = ((0x40U & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((0x20U & ((~ 
                                                  ((IData)(__PVT__compressed_6bit_vector) 
                                                   >> 5U)) 
                                                 << 5U)) 
                                       | (0x1fU & (IData)(__PVT__compressed_6bit_vector))));
    } else {
        vlSelf->__PVT__clz_plus1 = (((IData)((0x820U 
                                              == (0x820U 
                                                  & (IData)(__PVT__compressed_6bit_vector)))) 
                                     << 6U) | (0x1fU 
                                               & ((IData)(__PVT__compressed_6bit_vector) 
                                                  >> 6U)));
    }
}

VL_INLINE_OPT void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz__0\n"); );
    // Init
    IData/*19:0*/ __PVT__compressed_5bit_vector;
    SData/*11:0*/ __PVT__compressed_6bit_vector;
    // Body
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffffcULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | (IData)((IData)(
                                                      ((0U 
                                                        == 
                                                        (3U 
                                                         & (IData)(
                                                                   vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                   [1U])))
                                                        ? 2U
                                                        : 
                                                       ((1U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                    [1U])))
                                                         ? 1U
                                                         : 0U)))));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffff3ULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 2U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 2U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 2U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffffcfULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 4U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 4U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 4U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffff3fULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 6U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 6U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 6U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffcffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 8U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 8U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 8U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffff3ffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0xaU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0xaU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xaU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffcfffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0xcU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0xcU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xcU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffff3fffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0xeU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0xeU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xeU));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffcffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x10U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x10U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x10U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffff3ffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x12U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x12U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x12U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffcfffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x14U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x14U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x14U));
    vlSelf->__PVT__encoded_input = ((0xffffffffff3fffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x16U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x16U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x16U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffcffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x18U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x18U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x18U));
    vlSelf->__PVT__encoded_input = ((0xfffffffff3ffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x1aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x1aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1aU));
    vlSelf->__PVT__encoded_input = ((0xffffffffcfffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x1cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x1cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1cU));
    vlSelf->__PVT__encoded_input = ((0xffffffff3fffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x1eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x1eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1eU));
    vlSelf->__PVT__encoded_input = ((0xfffffffcffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x20U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x20U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x20U));
    vlSelf->__PVT__encoded_input = ((0xfffffff3ffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x22U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x22U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x22U));
    vlSelf->__PVT__encoded_input = ((0xffffffcfffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x24U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x24U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x24U));
    vlSelf->__PVT__encoded_input = ((0xffffff3fffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x26U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x26U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x26U));
    vlSelf->__PVT__encoded_input = ((0xfffffcffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x28U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x28U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x28U));
    vlSelf->__PVT__encoded_input = ((0xfffff3ffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x2aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x2aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2aU));
    vlSelf->__PVT__encoded_input = ((0xffffcfffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x2cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x2cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2cU));
    vlSelf->__PVT__encoded_input = ((0xffff3fffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x2eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x2eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2eU));
    vlSelf->__PVT__encoded_input = ((0xfffcffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x30U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x30U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x30U));
    vlSelf->__PVT__encoded_input = ((0xfff3ffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x32U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x32U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x32U));
    vlSelf->__PVT__encoded_input = ((0xffcfffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x34U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x34U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x34U));
    vlSelf->__PVT__encoded_input = ((0xff3fffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x36U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x36U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x36U));
    vlSelf->__PVT__encoded_input = ((0xfcffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x38U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x38U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x38U));
    vlSelf->__PVT__encoded_input = ((0xf3ffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x3aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x3aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3aU));
    vlSelf->__PVT__encoded_input = ((0xcfffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x3cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x3cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3cU));
    vlSelf->__PVT__encoded_input = ((0x3fffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                     [1U] 
                                                                     >> 0x3eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                      [1U] 
                                                                      >> 0x3eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3eU));
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 3U)))) {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 1U))) << 1U)) 
                  | (1U & (IData)(vlSelf->__PVT__encoded_input))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 2U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 7U)))) {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 5U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 4U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 6U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 9U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 8U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xaU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xfU)))) {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000ULL == (0xa000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0xdU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000ULL == (0xa000ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xeU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x13U)))) {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000ULL == (0xa0000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x11U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x10U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000ULL == (0xa0000ULL 
                                        & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x12U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000ULL == (0xa00000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x15U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x14U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000ULL == (0xa00000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x16U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000ULL == (0xa000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x19U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000ULL == (0xa000000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000ULL == (0xa0000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x1dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x1cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000ULL == (0xa0000000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000ULL == (0xa00000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x21U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x20U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000ULL == (0xa00000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x22U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x27U)))) {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000ULL == (0xa000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x25U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000ULL == (0xa000000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x26U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x29U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x28U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x2dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x2cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x33U)))) {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x31U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x30U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x32U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x37U)))) {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x35U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x34U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x36U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000000ULL == 
                           (0xa00000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x39U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x38U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000000ULL == (0xa00000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000000ULL == 
                           (0xa000000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x3dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x3cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000000ULL == (0xa000000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3eU))));
    }
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffff000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | (IData)((IData)(
                                                               (((IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2) 
                                                                 << 9U) 
                                                                | (((IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2) 
                                                                    << 6U) 
                                                                   | (((IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2) 
                                                                       << 3U) 
                                                                      | (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)))))));
    vlSelf->__PVT__compressed_3bit_vector = ((0xffffff000fffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0xcU));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfff000ffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x18U));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x24U));
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 5U)))) {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 2U))) << 2U)) 
                  | (3U & (IData)(vlSelf->__PVT__compressed_3bit_vector))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 3U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 8U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 6U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 9U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x11U)))) {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000ULL == (0x24000ULL 
                                          & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0xeU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000ULL == (0x24000ULL 
                                        & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0xfU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000ULL == (0x900000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x14U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x12U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000ULL == (0x900000ULL 
                                         & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x15U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x1dU)))) {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000ULL == (0x24000000ULL 
                                             & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x1aU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000ULL == (0x24000000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x1bU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000ULL == (0x900000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x20U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x1eU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000ULL == (0x900000000ULL 
                                            & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x21U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x29U)))) {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000000ULL == (0x24000000000ULL 
                                                & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x26U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000000ULL == (0x24000000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x27U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000000ULL == (0x900000000000ULL 
                                                 & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x2cU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x2aU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000000ULL == (0x900000000000ULL 
                                               & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x2dU))));
    }
    vlSelf->__PVT__compressed_4bit_vector = ((0xffff0000U 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0xcU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 8U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 4U) 
                                                      | (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)))));
    vlSelf->__PVT__compressed_4bit_vector = ((0xffffU 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0x1cU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 0x18U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 0x14U) 
                                                      | ((IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2) 
                                                         << 0x10U)))));
    if ((0x80U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 3U)) << 3U)) | (7U 
                                                & vlSelf->__PVT__compressed_4bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 4U)));
    }
    if ((0x8000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0xbU)) << 3U)) | (7U 
                                                  & (vlSelf->__PVT__compressed_4bit_vector 
                                                     >> 8U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0xcU)));
    }
    if ((0x800000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x880000U == (0x880000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x13U)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x10U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x880000U == (0x880000U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x14U)));
    }
    if ((vlSelf->__PVT__compressed_4bit_vector >> 0x1fU)) {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88000000U == (0x88000000U 
                                           & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x1bU)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x18U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88000000U == (0x88000000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x1cU)));
    }
    __PVT__compressed_5bit_vector = (((IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2) 
                                      << 0xfU) | (((IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2) 
                                                   << 0xaU) 
                                                  | (((IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2) 
                                                      << 5U) 
                                                     | (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2))));
    if ((0x200U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 4U)) << 4U)) | (0xfU 
                                                   & __PVT__compressed_5bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 5U)));
    }
    if ((0x80000U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 0xeU)) << 4U)) | 
                  (0xfU & (__PVT__compressed_5bit_vector 
                           >> 0xaU))));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 0xfU)));
    }
    __PVT__compressed_6bit_vector = (((IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2) 
                                      << 6U) | (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2));
    if ((0x800U & (IData)(__PVT__compressed_6bit_vector))) {
        vlSelf->__PVT__clz_plus1 = ((0x3fU & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((IData)((0x820U 
                                                == 
                                                (0x820U 
                                                 & (IData)(__PVT__compressed_6bit_vector)))) 
                                       << 6U));
        vlSelf->__PVT__clz_plus1 = ((0x40U & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((0x20U & ((~ 
                                                  ((IData)(__PVT__compressed_6bit_vector) 
                                                   >> 5U)) 
                                                 << 5U)) 
                                       | (0x1fU & (IData)(__PVT__compressed_6bit_vector))));
    } else {
        vlSelf->__PVT__clz_plus1 = (((IData)((0x820U 
                                              == (0x820U 
                                                  & (IData)(__PVT__compressed_6bit_vector)))) 
                                     << 6U) | (0x1fU 
                                               & ((IData)(__PVT__compressed_6bit_vector) 
                                                  >> 6U)));
    }
}

VL_INLINE_OPT void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz__0\n"); );
    // Init
    IData/*19:0*/ __PVT__compressed_5bit_vector;
    SData/*11:0*/ __PVT__compressed_6bit_vector;
    // Body
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffffcULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | (IData)((IData)(
                                                      ((0U 
                                                        == 
                                                        (3U 
                                                         & (IData)(vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input)))
                                                        ? 2U
                                                        : 
                                                       ((1U 
                                                         == 
                                                         (3U 
                                                          & (IData)(vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input)))
                                                         ? 1U
                                                         : 0U)))));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffff3ULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 2U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 2U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 2U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffffcfULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 4U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 4U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 4U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffff3fULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 6U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 6U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 6U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffcffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 8U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 8U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 8U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffff3ffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0xaU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0xaU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xaU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffcfffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0xcU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0xcU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xcU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffff3fffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0xeU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0xeU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xeU));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffcffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x10U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x10U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x10U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffff3ffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x12U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x12U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x12U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffcfffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x14U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x14U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x14U));
    vlSelf->__PVT__encoded_input = ((0xffffffffff3fffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x16U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x16U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x16U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffcffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x18U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x18U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x18U));
    vlSelf->__PVT__encoded_input = ((0xfffffffff3ffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x1aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x1aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1aU));
    vlSelf->__PVT__encoded_input = ((0xffffffffcfffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x1cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x1cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1cU));
    vlSelf->__PVT__encoded_input = ((0xffffffff3fffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x1eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x1eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1eU));
    vlSelf->__PVT__encoded_input = ((0xfffffffcffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x20U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x20U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x20U));
    vlSelf->__PVT__encoded_input = ((0xfffffff3ffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x22U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x22U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x22U));
    vlSelf->__PVT__encoded_input = ((0xffffffcfffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x24U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x24U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x24U));
    vlSelf->__PVT__encoded_input = ((0xffffff3fffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x26U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x26U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x26U));
    vlSelf->__PVT__encoded_input = ((0xfffffcffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x28U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x28U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x28U));
    vlSelf->__PVT__encoded_input = ((0xfffff3ffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x2aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x2aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2aU));
    vlSelf->__PVT__encoded_input = ((0xffffcfffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x2cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x2cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2cU));
    vlSelf->__PVT__encoded_input = ((0xffff3fffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x2eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x2eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2eU));
    vlSelf->__PVT__encoded_input = ((0xfffcffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x30U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x30U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x30U));
    vlSelf->__PVT__encoded_input = ((0xfff3ffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x32U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x32U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x32U));
    vlSelf->__PVT__encoded_input = ((0xffcfffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x34U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x34U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x34U));
    vlSelf->__PVT__encoded_input = ((0xff3fffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x36U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x36U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x36U));
    vlSelf->__PVT__encoded_input = ((0xfcffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x38U))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x38U))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x38U));
    vlSelf->__PVT__encoded_input = ((0xf3ffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x3aU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x3aU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3aU));
    vlSelf->__PVT__encoded_input = ((0xcfffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x3cU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x3cU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3cU));
    vlSelf->__PVT__encoded_input = ((0x3fffffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                     >> 0x3eU))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (vlSymsp->TOP.taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
                                                                      >> 0x3eU))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x3eU));
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 3U)))) {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 1U))) << 1U)) 
                  | (1U & (IData)(vlSelf->__PVT__encoded_input))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 2U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 7U)))) {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 5U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 4U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 6U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 9U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 8U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xaU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xfU)))) {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000ULL == (0xa000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0xdU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000ULL == (0xa000ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xeU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x13U)))) {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000ULL == (0xa0000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x11U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x10U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000ULL == (0xa0000ULL 
                                        & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x12U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000ULL == (0xa00000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x15U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x14U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000ULL == (0xa00000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x16U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000ULL == (0xa000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x19U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000ULL == (0xa000000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000ULL == (0xa0000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x1dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x1cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000ULL == (0xa0000000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000ULL == (0xa00000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x21U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x20U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000ULL == (0xa00000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x22U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x27U)))) {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000ULL == (0xa000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x25U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000ULL == (0xa000000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x26U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x29U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x28U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x2dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x2cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x33U)))) {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x31U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x30U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x32U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x37U)))) {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x35U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x34U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x36U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000000ULL == 
                           (0xa00000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x39U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x38U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000000ULL == (0xa00000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000000ULL == 
                           (0xa000000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x3dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x3cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000000ULL == (0xa000000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3eU))));
    }
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffff000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | (IData)((IData)(
                                                               (((IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2) 
                                                                 << 9U) 
                                                                | (((IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2) 
                                                                    << 6U) 
                                                                   | (((IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2) 
                                                                       << 3U) 
                                                                      | (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)))))));
    vlSelf->__PVT__compressed_3bit_vector = ((0xffffff000fffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0xcU));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfff000ffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x18U));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x24U));
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 5U)))) {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 2U))) << 2U)) 
                  | (3U & (IData)(vlSelf->__PVT__compressed_3bit_vector))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 3U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 8U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 6U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 9U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x11U)))) {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000ULL == (0x24000ULL 
                                          & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0xeU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000ULL == (0x24000ULL 
                                        & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0xfU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000ULL == (0x900000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x14U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x12U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000ULL == (0x900000ULL 
                                         & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x15U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x1dU)))) {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000ULL == (0x24000000ULL 
                                             & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x1aU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000ULL == (0x24000000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x1bU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000ULL == (0x900000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x20U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x1eU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000ULL == (0x900000000ULL 
                                            & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x21U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x29U)))) {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000000ULL == (0x24000000000ULL 
                                                & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x26U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000000ULL == (0x24000000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x27U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000000ULL == (0x900000000000ULL 
                                                 & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x2cU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x2aU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000000ULL == (0x900000000000ULL 
                                               & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x2dU))));
    }
    vlSelf->__PVT__compressed_4bit_vector = ((0xffff0000U 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0xcU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 8U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 4U) 
                                                      | (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)))));
    vlSelf->__PVT__compressed_4bit_vector = ((0xffffU 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0x1cU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 0x18U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 0x14U) 
                                                      | ((IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2) 
                                                         << 0x10U)))));
    if ((0x80U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 3U)) << 3U)) | (7U 
                                                & vlSelf->__PVT__compressed_4bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 4U)));
    }
    if ((0x8000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0xbU)) << 3U)) | (7U 
                                                  & (vlSelf->__PVT__compressed_4bit_vector 
                                                     >> 8U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0xcU)));
    }
    if ((0x800000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x880000U == (0x880000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x13U)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x10U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x880000U == (0x880000U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x14U)));
    }
    if ((vlSelf->__PVT__compressed_4bit_vector >> 0x1fU)) {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88000000U == (0x88000000U 
                                           & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x1bU)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x18U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88000000U == (0x88000000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x1cU)));
    }
    __PVT__compressed_5bit_vector = (((IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2) 
                                      << 0xfU) | (((IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2) 
                                                   << 0xaU) 
                                                  | (((IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2) 
                                                      << 5U) 
                                                     | (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2))));
    if ((0x200U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 4U)) << 4U)) | (0xfU 
                                                   & __PVT__compressed_5bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 5U)));
    }
    if ((0x80000U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 0xeU)) << 4U)) | 
                  (0xfU & (__PVT__compressed_5bit_vector 
                           >> 0xaU))));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 0xfU)));
    }
    __PVT__compressed_6bit_vector = (((IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2) 
                                      << 6U) | (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2));
    if ((0x800U & (IData)(__PVT__compressed_6bit_vector))) {
        vlSelf->__PVT__clz_plus1 = ((0x3fU & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((IData)((0x820U 
                                                == 
                                                (0x820U 
                                                 & (IData)(__PVT__compressed_6bit_vector)))) 
                                       << 6U));
        vlSelf->__PVT__clz_plus1 = ((0x40U & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((0x20U & ((~ 
                                                  ((IData)(__PVT__compressed_6bit_vector) 
                                                   >> 5U)) 
                                                 << 5U)) 
                                       | (0x1fU & (IData)(__PVT__compressed_6bit_vector))));
    } else {
        vlSelf->__PVT__clz_plus1 = (((IData)((0x820U 
                                              == (0x820U 
                                                  & (IData)(__PVT__compressed_6bit_vector)))) 
                                     << 6U) | (0x1fU 
                                               & ((IData)(__PVT__compressed_6bit_vector) 
                                                  >> 6U)));
    }
}

VL_INLINE_OPT void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz__0\n"); );
    // Init
    IData/*19:0*/ __PVT__compressed_5bit_vector;
    SData/*11:0*/ __PVT__compressed_6bit_vector;
    // Body
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffffcULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | (IData)((IData)(
                                                      ((0U 
                                                        == 
                                                        (3U 
                                                         & (IData)(
                                                                   (0x1fffffffffffffULL 
                                                                    & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                       >> 2U)))))
                                                        ? 2U
                                                        : 
                                                       ((1U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1fffffffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 2U)))))
                                                         ? 1U
                                                         : 0U)))));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffff3ULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7ffffffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 4U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7ffffffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 4U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 2U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffffcfULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1ffffffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 6U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1ffffffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 6U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 4U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffff3fULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7fffffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 8U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7fffffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 8U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 6U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffffcffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1fffffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0xaU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1fffffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0xaU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 8U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffff3ffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7ffffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0xcU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7ffffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0xcU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xaU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffffcfffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1ffffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0xeU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1ffffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0xeU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xcU));
    vlSelf->__PVT__encoded_input = ((0xffffffffffff3fffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7fffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x10U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7fffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x10U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0xeU));
    vlSelf->__PVT__encoded_input = ((0xfffffffffffcffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1fffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x12U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1fffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x12U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x10U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffff3ffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7ffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x14U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7ffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x14U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x12U));
    vlSelf->__PVT__encoded_input = ((0xffffffffffcfffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1ffffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x16U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1ffffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x16U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x14U));
    vlSelf->__PVT__encoded_input = ((0xffffffffff3fffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7fffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x18U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7fffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x18U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x16U));
    vlSelf->__PVT__encoded_input = ((0xfffffffffcffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1fffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x1aU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1fffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x1aU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x18U));
    vlSelf->__PVT__encoded_input = ((0xfffffffff3ffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7ffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x1cU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7ffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x1cU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1aU));
    vlSelf->__PVT__encoded_input = ((0xffffffffcfffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1ffffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x1eU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1ffffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x1eU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1cU));
    vlSelf->__PVT__encoded_input = ((0xffffffff3fffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7fffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x20U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7fffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x20U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x1eU));
    vlSelf->__PVT__encoded_input = ((0xfffffffcffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1fffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x22U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1fffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x22U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x20U));
    vlSelf->__PVT__encoded_input = ((0xfffffff3ffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7ffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x24U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7ffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x24U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x22U));
    vlSelf->__PVT__encoded_input = ((0xffffffcfffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1ffffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x26U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1ffffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x26U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x24U));
    vlSelf->__PVT__encoded_input = ((0xffffff3fffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7fffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x28U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7fffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x28U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x26U));
    vlSelf->__PVT__encoded_input = ((0xfffffcffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1fffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x2aU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1fffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x2aU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x28U));
    vlSelf->__PVT__encoded_input = ((0xfffff3ffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7ffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x2cU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7ffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x2cU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2aU));
    vlSelf->__PVT__encoded_input = ((0xffffcfffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1ffULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x2eU)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1ffULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x2eU)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2cU));
    vlSelf->__PVT__encoded_input = ((0xffff3fffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x7fULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x30U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x7fULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x30U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x2eU));
    vlSelf->__PVT__encoded_input = ((0xfffcffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (0x1fULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x32U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (0x1fULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x32U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x30U));
    vlSelf->__PVT__encoded_input = ((0xfff3ffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (7ULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x34U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (7ULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x34U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x32U));
    vlSelf->__PVT__encoded_input = ((0xffcfffffffffffffULL 
                                     & vlSelf->__PVT__encoded_input) 
                                    | ((QData)((IData)(
                                                       ((0U 
                                                         == 
                                                         (3U 
                                                          & (IData)(
                                                                    (1ULL 
                                                                     & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                        >> 0x36U)))))
                                                         ? 2U
                                                         : 
                                                        ((1U 
                                                          == 
                                                          (3U 
                                                           & (IData)(
                                                                     (1ULL 
                                                                      & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                                                         >> 0x36U)))))
                                                          ? 1U
                                                          : 0U)))) 
                                       << 0x34U));
    vlSelf->__PVT__encoded_input = (0x80000000000000ULL 
                                    | (0xff3fffffffffffffULL 
                                       & vlSelf->__PVT__encoded_input));
    vlSelf->__PVT__encoded_input = (0x200000000000000ULL 
                                    | (0xfcffffffffffffffULL 
                                       & vlSelf->__PVT__encoded_input));
    vlSelf->__PVT__encoded_input = (0x800000000000000ULL 
                                    | (0xf3ffffffffffffffULL 
                                       & vlSelf->__PVT__encoded_input));
    vlSelf->__PVT__encoded_input = (0x2000000000000000ULL 
                                    | (0xcfffffffffffffffULL 
                                       & vlSelf->__PVT__encoded_input));
    vlSelf->__PVT__encoded_input = (0x8000000000000000ULL 
                                    | (0x3fffffffffffffffULL 
                                       & vlSelf->__PVT__encoded_input));
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 3U)))) {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 1U))) << 1U)) 
                  | (1U & (IData)(vlSelf->__PVT__encoded_input))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xaULL == (0xaULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 2U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 7U)))) {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 5U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 4U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0ULL == (0xa0ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 6U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 9U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 8U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00ULL == (0xa00ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xaU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0xfU)))) {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000ULL == (0xa000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0xdU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000ULL == (0xa000ULL & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0xeU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x13U)))) {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000ULL == (0xa0000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x11U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x10U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000ULL == (0xa0000ULL 
                                        & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x12U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000ULL == (0xa00000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x15U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x14U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000ULL == (0xa00000ULL 
                                         & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x16U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000ULL == (0xa000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x19U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000ULL == (0xa000000ULL 
                                          & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x1fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000ULL == (0xa0000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x1dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x1cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000ULL == (0xa0000000ULL 
                                           & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x1eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000ULL == (0xa00000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x21U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x20U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000ULL == (0xa00000000ULL 
                                            & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x22U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x27U)))) {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000ULL == (0xa000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x25U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000ULL == (0xa000000000ULL 
                                             & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x26U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x29U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x28U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000ULL == (0xa0000000000ULL 
                                              & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x2dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x2cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000ULL == (0xa00000000000ULL 
                                               & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x2eU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x33U)))) {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x31U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x30U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000ULL == (0xa000000000000ULL 
                                                & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x32U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x37U)))) {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x35U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x34U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa0000000000000ULL == (0xa0000000000000ULL 
                                                 & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x36U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3bU)))) {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa00000000000000ULL == 
                           (0xa00000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x39U))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x38U)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa00000000000000ULL == (0xa00000000000000ULL 
                                                  & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3aU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__encoded_input 
                       >> 0x3fU)))) {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((3U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((IData)((0xa000000000000000ULL == 
                           (0xa000000000000000ULL & vlSelf->__PVT__encoded_input))) 
                  << 2U));
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = ((4U & (IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2)) 
               | ((2U & ((~ (IData)((vlSelf->__PVT__encoded_input 
                                     >> 0x3dU))) << 1U)) 
                  | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                   >> 0x3cU)))));
    } else {
        vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 
            = (((IData)((0xa000000000000000ULL == (0xa000000000000000ULL 
                                                   & vlSelf->__PVT__encoded_input))) 
                << 2U) | (1U & (IData)((vlSelf->__PVT__encoded_input 
                                        >> 0x3eU))));
    }
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffff000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | (IData)((IData)(
                                                               (((IData)(vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2) 
                                                                 << 9U) 
                                                                | (((IData)(vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2) 
                                                                    << 6U) 
                                                                   | (((IData)(vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2) 
                                                                       << 3U) 
                                                                      | (IData)(vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2)))))));
    vlSelf->__PVT__compressed_3bit_vector = ((0xffffff000fffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0xcU));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfff000ffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x18U));
    vlSelf->__PVT__compressed_3bit_vector = ((0xfffffffffULL 
                                              & vlSelf->__PVT__compressed_3bit_vector) 
                                             | ((QData)((IData)(
                                                                (((IData)(vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2) 
                                                                  << 9U) 
                                                                 | (((IData)(vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2) 
                                                                     << 6U) 
                                                                    | (((IData)(vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2) 
                                                                        << 3U) 
                                                                       | (IData)(vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2)))))) 
                                                << 0x24U));
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 5U)))) {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 2U))) << 2U)) 
                  | (3U & (IData)(vlSelf->__PVT__compressed_3bit_vector))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24ULL == (0x24ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 3U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0xbU)))) {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 8U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 6U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900ULL == (0x900ULL & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 9U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x11U)))) {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000ULL == (0x24000ULL 
                                          & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0xeU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0xcU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000ULL == (0x24000ULL 
                                        & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0xfU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x17U)))) {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000ULL == (0x900000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x14U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x12U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000ULL == (0x900000ULL 
                                         & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x15U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x1dU)))) {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000ULL == (0x24000000ULL 
                                             & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x1aU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x18U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000ULL == (0x24000000ULL 
                                           & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x1bU))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x23U)))) {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000ULL == (0x900000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x20U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x1eU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000ULL == (0x900000000ULL 
                                            & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x21U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x29U)))) {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x24000000000ULL == (0x24000000000ULL 
                                                & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x26U))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x24U)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x24000000000ULL == (0x24000000000ULL 
                                              & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x27U))));
    }
    if ((1U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                       >> 0x2fU)))) {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((7U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((IData)((0x900000000000ULL == (0x900000000000ULL 
                                                 & vlSelf->__PVT__compressed_3bit_vector))) 
                  << 3U));
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = ((8U & (IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2)) 
               | ((4U & ((~ (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                     >> 0x2cU))) << 2U)) 
                  | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                   >> 0x2aU)))));
    } else {
        vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 
            = (((IData)((0x900000000000ULL == (0x900000000000ULL 
                                               & vlSelf->__PVT__compressed_3bit_vector))) 
                << 3U) | (3U & (IData)((vlSelf->__PVT__compressed_3bit_vector 
                                        >> 0x2dU))));
    }
    vlSelf->__PVT__compressed_4bit_vector = ((0xffff0000U 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0xcU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 8U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 4U) 
                                                      | (IData)(vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2)))));
    vlSelf->__PVT__compressed_4bit_vector = ((0xffffU 
                                              & vlSelf->__PVT__compressed_4bit_vector) 
                                             | (((IData)(vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2) 
                                                 << 0x1cU) 
                                                | (((IData)(vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2) 
                                                    << 0x18U) 
                                                   | (((IData)(vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2) 
                                                       << 0x14U) 
                                                      | ((IData)(vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2) 
                                                         << 0x10U)))));
    if ((0x80U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 3U)) << 3U)) | (7U 
                                                & vlSelf->__PVT__compressed_4bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88U == (0x88U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 4U)));
    }
    if ((0x8000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0xbU)) << 3U)) | (7U 
                                                  & (vlSelf->__PVT__compressed_4bit_vector 
                                                     >> 8U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x8800U == (0x8800U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0xcU)));
    }
    if ((0x800000U & vlSelf->__PVT__compressed_4bit_vector)) {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x880000U == (0x880000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x13U)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x10U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x880000U == (0x880000U & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x14U)));
    }
    if ((vlSelf->__PVT__compressed_4bit_vector >> 0x1fU)) {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0xfU & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((IData)((0x88000000U == (0x88000000U 
                                           & vlSelf->__PVT__compressed_4bit_vector))) 
                  << 4U));
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = ((0x10U & (IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2)) 
               | ((8U & ((~ (vlSelf->__PVT__compressed_4bit_vector 
                             >> 0x1bU)) << 3U)) | (7U 
                                                   & (vlSelf->__PVT__compressed_4bit_vector 
                                                      >> 0x18U))));
    } else {
        vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 
            = (((IData)((0x88000000U == (0x88000000U 
                                         & vlSelf->__PVT__compressed_4bit_vector))) 
                << 4U) | (7U & (vlSelf->__PVT__compressed_4bit_vector 
                                >> 0x1cU)));
    }
    __PVT__compressed_5bit_vector = (((IData)(vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2) 
                                      << 0xfU) | (((IData)(vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2) 
                                                   << 0xaU) 
                                                  | (((IData)(vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2) 
                                                      << 5U) 
                                                     | (IData)(vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2))));
    if ((0x200U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 4U)) << 4U)) | (0xfU 
                                                   & __PVT__compressed_5bit_vector)));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x210U == (0x210U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 5U)));
    }
    if ((0x80000U & __PVT__compressed_5bit_vector)) {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x1fU & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                  << 5U));
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = ((0x20U & (IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2)) 
               | ((0x10U & ((~ (__PVT__compressed_5bit_vector 
                                >> 0xeU)) << 4U)) | 
                  (0xfU & (__PVT__compressed_5bit_vector 
                           >> 0xaU))));
    } else {
        vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 
            = (((IData)((0x84000U == (0x84000U & __PVT__compressed_5bit_vector))) 
                << 5U) | (0xfU & (__PVT__compressed_5bit_vector 
                                  >> 0xfU)));
    }
    __PVT__compressed_6bit_vector = (((IData)(vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2) 
                                      << 6U) | (IData)(vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2));
    if ((0x800U & (IData)(__PVT__compressed_6bit_vector))) {
        vlSelf->__PVT__clz_plus1 = ((0x3fU & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((IData)((0x820U 
                                                == 
                                                (0x820U 
                                                 & (IData)(__PVT__compressed_6bit_vector)))) 
                                       << 6U));
        vlSelf->__PVT__clz_plus1 = ((0x40U & (IData)(vlSelf->__PVT__clz_plus1)) 
                                    | ((0x20U & ((~ 
                                                  ((IData)(__PVT__compressed_6bit_vector) 
                                                   >> 5U)) 
                                                 << 5U)) 
                                       | (0x1fU & (IData)(__PVT__compressed_6bit_vector))));
    } else {
        vlSelf->__PVT__clz_plus1 = (((IData)((0x820U 
                                              == (0x820U 
                                                  & (IData)(__PVT__compressed_6bit_vector)))) 
                                     << 6U) | (0x1fU 
                                               & ((IData)(__PVT__compressed_6bit_vector) 
                                                  >> 6U)));
    }
}
