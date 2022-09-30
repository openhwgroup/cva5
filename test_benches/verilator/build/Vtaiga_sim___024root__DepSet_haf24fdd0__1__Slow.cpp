// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim__Syms.h"
#include "Vtaiga_sim___024root.h"

VL_ATTR_COLD void Vtaiga_sim___024root___settle__TOP__1(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___settle__TOP__1\n"); );
    // Init
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__contiguous_retire;
    CData/*1:0*/ taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_inuse;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0;
    QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT____Vlvbound_hdcd812e1__0;
    CData/*4:0*/ taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_fflags;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__20__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__21__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__22__Vfuncout;
    // Body
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_rs_wb_group[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_rs_wb_group
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_rs_wb_group[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_rs_wb_group
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_rs_wb_group[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_rs_wb_group
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_rs_wb_group[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_rs_wb_group
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_rs_wb_group[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_rs_wb_group
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_phys_rs_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_phys_rs_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_phys_rs_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_phys_rs_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__1__KET____DOT__reg_group__read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__1__KET____DOT__reg_group__read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_rs_wb_group[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_rs_wb_group
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_rs_wb_group[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_rs_wb_group
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_rs_wb_group[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_rs_wb_group
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_phys_rs_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = (0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = (0xf0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_is_post_issue[0U] 
        = (0U < (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__post_issue_count));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_ready_to_retire[0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_is_post_issue
           [0U] & (~ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse
                   [0U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next[0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_ready_to_retire
           [0U] & ((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd)) 
                   | (~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next) 
                         >> 7U))));
    taiga_sim__DOT__cpu__DOT__id_block__DOT__contiguous_retire 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
           [0U] & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                      >> 0xaU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (0x80U & ((0xffffff80U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
                       | ((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
                           [0U] & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd)) 
                          << 7U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0xf3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (0xcU & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next) 
                        >> 2U) + vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
                       [0U]) << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0xfdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (2U & ((0xfffffffeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
                    | (((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
                         [0U] & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd)) 
                        & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_wb2_float)) 
                       << 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0xfeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next) 
                    | (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
                       [0U] & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_accu_fcsr)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_is_post_issue[1U] 
        = (1U < (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__post_issue_count));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_ready_to_retire[1U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_is_post_issue
            [1U] & (IData)(taiga_sim__DOT__cpu__DOT__id_block__DOT__contiguous_retire)) 
           & (~ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse
              [1U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next[1U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_ready_to_retire
           [1U] & ((~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd) 
                       >> 1U)) | (~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next) 
                                     >> 7U))));
    taiga_sim__DOT__cpu__DOT__id_block__DOT__contiguous_retire 
        = ((IData)(taiga_sim__DOT__cpu__DOT__id_block__DOT__contiguous_retire) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
              [1U] & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                         >> 0xaU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (0x80U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next) 
                       | ((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
                           [1U] << 7U) & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd) 
                                          << 6U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0xf3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (0xcU & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next) 
                        >> 2U) + vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
                       [1U]) << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0xfdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (2U & ((0xfffffffeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
                    | (0xfffffffeU & (((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
                                        [1U] << 1U) 
                                       & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd)) 
                                      & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_wb2_float))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0xfeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next) 
                    | (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next
                       [1U] & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_accu_fcsr) 
                               >> 1U)))));
    taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_inuse 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse
            [1U] << 1U) | vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse
           [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__1__KET____DOT__reg_group__data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__1__KET____DOT__reg_group__DOT__register_file_bank
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__1__KET____DOT__reg_group__read_addr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__1__KET____DOT__reg_group__data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__1__KET____DOT__reg_group__DOT__register_file_bank
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__1__KET____DOT__reg_group__read_addr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next 
        = ((0x8fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next)) 
           | (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next
              [(1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__encoder_rom) 
                      >> ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd) 
                          & (~ (IData)(taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_inuse)))))] 
              << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_data_set[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_data_set[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_data_set[1U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__1__KET____DOT__reg_group__data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_data_set[1U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__1__KET____DOT__reg_group__data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [4U];
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT____Vlvbound_hdcd812e1__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data[0U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT____Vlvbound_hdcd812e1__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT____Vlvbound_hdcd812e1__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data[1U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT____Vlvbound_hdcd812e1__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT____Vlvbound_hdcd812e1__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data[2U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT____Vlvbound_hdcd812e1__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__21__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite) 
           & (0x3000000000ULL == (0xff000000000ULL 
                                  & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__20__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite) 
           & (0x1000000000ULL == (0xff000000000ULL 
                                  & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_fflags 
        = (0x1fU & (((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__20__Vfuncout) 
                     | (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__21__Vfuncout))
                     ? vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr
                     : (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__fcsr 
                        | ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next))
                            ? ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out))
                                ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__fp_unit_fflags_table
                               [(7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out) 
                                       >> 1U))] : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__unit_fflags_table
                               [(7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out) 
                                       >> 1U))]) : 0U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_data_set[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_data_set[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_data_set[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [6U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__22__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite) 
           & (0x3000000000ULL == (0xff000000000ULL 
                                  & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_fcsr 
        = ((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__22__Vfuncout)
            ? vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr
            : (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_frm) 
                << 5U) | (IData)(taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_fflags)));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [6U];
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [4U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[4U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [5U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[5U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [4U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[4U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [5U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[5U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [4U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[4U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [5U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[5U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [4U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[4U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [5U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[5U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT____Vlvbound_h46f4d77e__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [4U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [5U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [6U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [7U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [4U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [5U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [6U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [7U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [4U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [5U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [6U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [7U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [4U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [5U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [6U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [7U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] = 0U;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [3U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [3U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [3U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [3U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_ha1a1b3b6__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [1U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.inuse[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [2U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.inuse[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[6U] = 0U;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [3U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [3U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [3U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [3U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [5U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][5U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[5U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [5U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][5U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[5U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [5U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][5U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[5U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [5U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][5U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[5U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [6U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][6U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[6U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [6U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][6U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[6U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [6U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][6U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[6U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [6U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][6U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[6U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hc88fabce__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[0U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[1U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[2U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[3U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[4U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0;
    taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[5U] 
        = taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_h548b5214__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__operands_ready 
        = (1U & ((~ (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.inuse
                     [0U] & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                             >> 0x15U))) & (~ (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.inuse
                                               [1U] 
                                               & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                  >> 0x14U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
        = ((0xffffc3ffU & vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U]) 
           | (0xfffffc00U & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.inuse
                              [1U] << 0xdU) | (((0x80U 
                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U])
                                                 ? 
                                                vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rd_to_id_table
                                                [(0x1fU 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                                     >> 0x12U))]
                                                 : 
                                                vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rd_to_id_table
                                                [(0x1fU 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                                     >> 0x12U))]) 
                                               << 0xaU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [2U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.inuse[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [3U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.inuse[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [4U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.inuse[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict 
        = (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.inuse
           [0U] & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                   >> 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict 
        = (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.inuse
           [1U] & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                   >> 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict 
        = (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.inuse
           [2U] & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                   >> 0xbU));
    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[0U] 
        = (((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                    [1U]) << 1U) | vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.inuse
           [1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[1U] 
        = (((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                    [1U]) >> 0x1fU) | ((IData)((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                                                [1U] 
                                                >> 0x20U)) 
                                       << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
        = ((0xfffffffcU & vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U]) 
           | ((2U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                     >> 6U)) | ((IData)((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                                         [1U] >> 0x20U)) 
                                >> 0x1fU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_operands_ready 
        = (1U & (((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict)) 
                  & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict))) 
                 & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[4U] 
           + VL_EXTENDS_II(32,12, (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                   >> 0x14U)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__1__KET__.ready 
        = (1U & ((((vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                    >> 0x10U) | (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_full))) 
                  & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__fence_hold))) 
                 & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__exception__BRA__0__KET__.valid))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_valid 
        = (((((vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
               >> 0xcU) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__operands_ready)) 
             & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_operands_ready)) 
            & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                  >> 0x10U))) & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__pre_issue_exception_pending)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash 
        = ((0xeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash)) 
           | (1U & VL_REDXOR_16((0x440U & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash 
        = ((0xdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash)) 
           | (2U & (VL_REDXOR_16((0x888U & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address)) 
                    << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash 
        = ((3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash)) 
           | (0xcU & ((0x3ffffffcU & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address 
                                      >> 2U)) ^ (0x3fffffcU 
                                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address 
                                                    >> 6U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be = 0U;
    if ((0U == (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                      >> 0x11U)))) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be 
            = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be) 
               | (0xfU & ((IData)(1U) << (3U & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address))));
    } else if ((1U == (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                             >> 0x11U)))) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be 
            = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be) 
               | (0xfU & ((IData)(1U) << (3U & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address))));
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be 
            = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be) 
               | (0xfU & ((IData)(1U) << (1U | (2U 
                                                & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address)))));
    } else {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be = 0xfU;
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be 
        = (0xfU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be) 
                   | (- (IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                       >> 1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready 
        = ((0x7f0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready)) 
           | (1U | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__stage1_advance) 
                     << 3U) | ((4U & ((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__busy)) 
                                      << 2U)) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__1__KET__.ready) 
                                                 << 1U)))));
}

VL_ATTR_COLD void Vtaiga_sim___024root___settle__TOP__2(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___settle__TOP__2\n"); );
    // Init
    SData/*10:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready;
    CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index_one_hot;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_request;
    CData/*2:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vlvbound_hea6c5ab7__0;
    VlWide<13>/*415:0*/ __Vtemp_h29a51113__0;
    VlWide<4>/*127:0*/ __Vtemp_hcb8805f9__0;
    VlWide<3>/*95:0*/ __Vtemp_h0faf1974__0;
    // Body
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__clz_with_prepended_0s 
        = ((0x7c0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__clz_with_prepended_0s)) 
           | (0x3fU & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz.__PVT__clz_plus1)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__clz_with_prepended_0s 
        = ((0x7c0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__clz_with_prepended_0s)) 
           | (0x3fU & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz.__PVT__clz_plus1)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__clz_with_prepended_0s 
        = ((0x7c0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__clz_with_prepended_0s)) 
           | (0x3fU & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz.__PVT__clz_plus1)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__clz_with_prepended_0s 
        = ((0x7c0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__clz_with_prepended_0s)) 
           | (0x3fU & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz.__PVT__clz_plus1)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__clz_with_prepended_0s 
        = ((0x7c0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__clz_with_prepended_0s)) 
           | (0x3fU & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz.__PVT__clz_plus1)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz[0U] 
        = ((0xffe003fffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz
            [0U]) | ((QData)((IData)((0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                                                [0U]
                                                 ? 
                                                (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case
                                                 [0U]
                                                  ? 0U
                                                  : 
                                                 (0x7ffU 
                                                  & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__clz_with_prepended_0s) 
                                                     - (IData)(0xbU))))
                                                 : (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb.clz))))) 
                     << 0x16U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz[0U] 
        = ((0xfffffc007ffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz
            [0U]) | ((QData)((IData)((0x7ffU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__clz_with_prepended_0s) 
                                                 & (- (IData)(
                                                              (1U 
                                                               & (~ 
                                                                  vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                                                                  [1U]))))) 
                                                - (0xbU 
                                                   & (- (IData)(
                                                                (1U 
                                                                 & (~ 
                                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                                                                    [1U]))))))))) 
                     << 0xbU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt 
        = (0x7ffU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__clz_with_prepended_0s) 
                      & (- (IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[7U] 
                                          >> 6U))))) 
                     - (0xbU & (- (IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[7U] 
                                                 >> 6U)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt 
        = (0x7ffU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__clz_with_prepended_0s) 
                      & (- (IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[7U] 
                                          >> 6U))))) 
                     - (0xbU & (- (IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[7U] 
                                                 >> 6U)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz[0U] 
        = ((0xffffffff800ULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz
            [0U]) | (IData)((IData)((0x7ffU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__clz_with_prepended_0s) 
                                                & (- (IData)(
                                                             (1U 
                                                              & (~ 
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case
                                                                 [1U]))))) 
                                               - ((
                                                   (0U 
                                                    != 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                                    [1U])
                                                    ? 0xbU
                                                    : 0xffffffd7U) 
                                                  & (- (IData)(
                                                               (1U 
                                                                & (~ 
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case
                                                                   [1U]))))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT____Vcellout__pre_normalize_rs1__frac_normalized 
        = ((0x34U >= (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt))
            ? (0x1fffffffffffffULL & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
                                      << (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt)))
            : 0ULL);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT____Vcellout__pre_normalize_rs2__frac_normalized 
        = ((0x34U >= (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt))
            ? (0x1fffffffffffffULL & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
                                      << (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt)))
            : 0ULL);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[6U] 
        = ((0x1dfffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[6U]) 
           | (0x1ffffU & ((IData)((0U != vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done
                                   [0U])) << 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[6U] 
        = ((0x3fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[6U]) 
           | (0x1ffffU & (((0xbU >= (0xfU & ((IData)(3U) 
                                             * vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                             [0U])))
                            ? (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id
                                     [0U] >> (0xfU 
                                              & ((IData)(3U) 
                                                 * 
                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                 [0U]))))
                            : 0U) << 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U] 
        = ((0xfffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U]) 
           | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd
                       [0U][vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                       [0U]]) << 0xdU) | (0x1000U & 
                                          ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow
                                            [0U] >> 
                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                            [0U]) << 0xcU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[5U] 
        = ((0xfffU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd
                              [0U][vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                              [0U]]) >> 0x13U)) | (
                                                   (0x1000U 
                                                    & ((IData)(
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd
                                                               [0U]
                                                               [
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                               [0U]]) 
                                                       >> 0x13U)) 
                                                   | ((IData)(
                                                              (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd
                                                               [0U]
                                                               [
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                               [0U]] 
                                                               >> 0x20U)) 
                                                      << 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[6U] 
        = ((0x1e000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[6U]) 
           | (0x1ffffU & ((0xfffU & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd
                                              [0U][
                                              vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                              [0U]] 
                                              >> 0x20U)) 
                                     >> 0x13U)) | (0x1000U 
                                                   & ((IData)(
                                                              (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd
                                                               [0U]
                                                               [
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                               [0U]] 
                                                               >> 0x20U)) 
                                                      >> 0x13U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U] 
        = ((0xfffff07fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U]) 
           | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_fflags
              [0U][vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
              [0U]] << 7U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U] 
        = ((0xffffff8fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U]) 
           | (((0xbU >= (0xfU & ((IData)(3U) * vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                 [0U]))) ? (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm
                                                  [0U] 
                                                  >> 
                                                  (0xfU 
                                                   & ((IData)(3U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                      [0U]))))
                : 0U) << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U] 
        = ((0xfffffff3U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U]) 
           | (0xfffffffcU & ((8U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry
                                     [0U] >> vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                     [0U]) << 3U)) 
                             | (4U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe
                                       [0U] >> vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                       [0U]) << 2U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U] 
        = ((0xfffffffdU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U]) 
           | (2U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden
                     [0U] >> vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                     [0U]) << 1U)));
    __Vtemp_h29a51113__0[0U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][0U];
    __Vtemp_h29a51113__0[1U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][1U];
    __Vtemp_h29a51113__0[2U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][2U];
    __Vtemp_h29a51113__0[3U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][3U];
    __Vtemp_h29a51113__0[4U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][4U];
    __Vtemp_h29a51113__0[5U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][5U];
    __Vtemp_h29a51113__0[6U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][6U];
    __Vtemp_h29a51113__0[7U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][7U];
    __Vtemp_h29a51113__0[8U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][8U];
    __Vtemp_h29a51113__0[9U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][9U];
    __Vtemp_h29a51113__0[0xaU] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][0xaU];
    __Vtemp_h29a51113__0[0xbU] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][0xbU];
    __Vtemp_h29a51113__0[0xcU] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
        [0U][0xcU];
    if ((0x19fU >= (0x1ffU & ((IData)(0x68U) * vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                              [0U])))) {
        __Vtemp_hcb8805f9__0[1U] = (((0U == (0x1fU 
                                             & ((IData)(0x68U) 
                                                * vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                [0U])))
                                      ? 0U : (__Vtemp_h29a51113__0[
                                              ((IData)(2U) 
                                               + (0xfU 
                                                  & (((IData)(0x68U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                      [0U]) 
                                                     >> 5U)))] 
                                              << ((IData)(0x20U) 
                                                  - 
                                                  (0x1fU 
                                                   & ((IData)(0x68U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                      [0U]))))) 
                                    | (__Vtemp_h29a51113__0[
                                       ((IData)(1U) 
                                        + (0xfU & (
                                                   ((IData)(0x68U) 
                                                    * 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                    [0U]) 
                                                   >> 5U)))] 
                                       >> (0x1fU & 
                                           ((IData)(0x68U) 
                                            * vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                            [0U]))));
        __Vtemp_hcb8805f9__0[2U] = (((0U == (0x1fU 
                                             & ((IData)(0x68U) 
                                                * vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                [0U])))
                                      ? 0U : (__Vtemp_h29a51113__0[
                                              ((IData)(3U) 
                                               + (0xfU 
                                                  & (((IData)(0x68U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                      [0U]) 
                                                     >> 5U)))] 
                                              << ((IData)(0x20U) 
                                                  - 
                                                  (0x1fU 
                                                   & ((IData)(0x68U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                      [0U]))))) 
                                    | (__Vtemp_h29a51113__0[
                                       ((IData)(2U) 
                                        + (0xfU & (
                                                   ((IData)(0x68U) 
                                                    * 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                    [0U]) 
                                                   >> 5U)))] 
                                       >> (0x1fU & 
                                           ((IData)(0x68U) 
                                            * vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                            [0U]))));
        __Vtemp_hcb8805f9__0[3U] = (0xffU & (((0U == 
                                               (0x1fU 
                                                & ((IData)(0x68U) 
                                                   * 
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                   [0U])))
                                               ? 0U
                                               : (__Vtemp_h29a51113__0[
                                                  ((IData)(4U) 
                                                   + 
                                                   (0xfU 
                                                    & (((IData)(0x68U) 
                                                        * 
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                        [0U]) 
                                                       >> 5U)))] 
                                                  << 
                                                  ((IData)(0x20U) 
                                                   - 
                                                   (0x1fU 
                                                    & ((IData)(0x68U) 
                                                       * 
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                       [0U]))))) 
                                             | (__Vtemp_h29a51113__0[
                                                ((IData)(3U) 
                                                 + 
                                                 (0xfU 
                                                  & (((IData)(0x68U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                      [0U]) 
                                                     >> 5U)))] 
                                                >> 
                                                (0x1fU 
                                                 & ((IData)(0x68U) 
                                                    * 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                    [0U])))));
    } else {
        __Vtemp_hcb8805f9__0[1U] = 0U;
        __Vtemp_hcb8805f9__0[2U] = 0U;
        __Vtemp_hcb8805f9__0[3U] = 0U;
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[0U] 
        = ((0x1ffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[0U]) 
           | (((0x19fU >= (0x1ffU & ((IData)(0x68U) 
                                     * vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                     [0U]))) ? (((0U 
                                                  == 
                                                  (0x1fU 
                                                   & ((IData)(0x68U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                      [0U])))
                                                  ? 0U
                                                  : 
                                                 (__Vtemp_h29a51113__0[
                                                  ((IData)(1U) 
                                                   + 
                                                   (0xfU 
                                                    & (((IData)(0x68U) 
                                                        * 
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                        [0U]) 
                                                       >> 5U)))] 
                                                  << 
                                                  ((IData)(0x20U) 
                                                   - 
                                                   (0x1fU 
                                                    & ((IData)(0x68U) 
                                                       * 
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                       [0U]))))) 
                                                | (__Vtemp_h29a51113__0[
                                                   (0xfU 
                                                    & (((IData)(0x68U) 
                                                        * 
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                        [0U]) 
                                                       >> 5U))] 
                                                   >> 
                                                   (0x1fU 
                                                    & ((IData)(0x68U) 
                                                       * 
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                       [0U]))))
                : 0U) << 0x19U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[1U] 
        = ((((0x19fU >= (0x1ffU & ((IData)(0x68U) * 
                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                   [0U]))) ? (((0U 
                                                == 
                                                (0x1fU 
                                                 & ((IData)(0x68U) 
                                                    * 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                    [0U])))
                                                ? 0U
                                                : (
                                                   __Vtemp_h29a51113__0[
                                                   ((IData)(1U) 
                                                    + 
                                                    (0xfU 
                                                     & (((IData)(0x68U) 
                                                         * 
                                                         vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                         [0U]) 
                                                        >> 5U)))] 
                                                   << 
                                                   ((IData)(0x20U) 
                                                    - 
                                                    (0x1fU 
                                                     & ((IData)(0x68U) 
                                                        * 
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                        [0U]))))) 
                                              | (__Vtemp_h29a51113__0[
                                                 (0xfU 
                                                  & (((IData)(0x68U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                      [0U]) 
                                                     >> 5U))] 
                                                 >> 
                                                 (0x1fU 
                                                  & ((IData)(0x68U) 
                                                     * 
                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                     [0U]))))
              : 0U) >> 7U) | (__Vtemp_hcb8805f9__0[1U] 
                              << 0x19U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[2U] 
        = ((__Vtemp_hcb8805f9__0[1U] >> 7U) | (__Vtemp_hcb8805f9__0[2U] 
                                               << 0x19U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[3U] 
        = ((__Vtemp_hcb8805f9__0[2U] >> 7U) | (__Vtemp_hcb8805f9__0[3U] 
                                               << 0x19U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U] 
        = ((0xfffffffeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[4U]) 
           | (__Vtemp_hcb8805f9__0[3U] >> 7U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[0U] 
        = ((0xfe003fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[0U]) 
           | (((0x2bU >= (0x3fU & ((IData)(0xbU) * 
                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                   [0U]))) ? (0x7ffU 
                                              & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz
                                                         [0U] 
                                                         >> 
                                                         (0x3fU 
                                                          & ((IData)(0xbU) 
                                                             * 
                                                             vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                             [0U])))))
                : 0U) << 0xeU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[0U] 
        = ((0xffffcfffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[0U]) 
           | (0xfffff000U & ((0x2000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal
                                          [0U] >> vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                          [0U]) << 0xdU)) 
                             | (0x1000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift
                                            [0U] >> 
                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                            [0U]) << 0xcU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[0U] 
        = ((0xfffff001U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[0U]) 
           | (((0x2bU >= (0x3fU & ((IData)(0xbU) * 
                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                   [0U]))) ? (0x7ffU 
                                              & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt
                                                         [0U] 
                                                         >> 
                                                         (0x3fU 
                                                          & ((IData)(0xbU) 
                                                             * 
                                                             vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                                                             [0U])))))
                : 0U) << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack[0U] = 0U;
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vlvbound_hea6c5ab7__0 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_norm) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet[6U] 
              >> 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack[0U] 
        = (((~ ((IData)(1U) << vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                [0U])) & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack
            [0U]) | (0xfU & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vlvbound_hea6c5ab7__0) 
                             << vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel
                             [0U])));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb.ack 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack
            [0U] >> 2U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__done_r));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_wb.ack 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack
            [0U] >> 2U) & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
           [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage[1U] 
        = (1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack
                 [0U] | (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done
                         [1U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__advance 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack
                  [0U] >> 3U) | (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.done))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[2U] 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack
                  [0U] >> 1U) | (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done
                                 [2U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__advance 
        = (1U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                  [0U]) | (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_wb.ack)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage[0U] 
        = (1U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done
                  [0U]) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
                 [1U]));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.pop 
        = (((~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U] 
                >> 0x18U)) & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.valid)) 
           & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
           [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__advance;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[0U] 
        = (1U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done
                  [0U]) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                 [1U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[1U] 
        = (1U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done
                  [1U]) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
                 [2U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready[0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage
           [0U] & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.valid)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__add_issue.new_request 
        = ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
            ? ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U] 
                >> 0xfU) & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage
               [0U]) : (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.pop));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready 
        = ((0xffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready)) 
           | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready
               [3U] << 0xaU) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready
                                 [2U] << 9U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready
                                                [1U] 
                                                << 8U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready 
        = ((0x70fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready)) 
           | (0x60U | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready
                        [0U] << 7U) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__4__KET__.ready) 
                                       << 4U))));
    taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready));
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_operand_stall 
        = ((((vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
              >> 0xcU) & (0U == (0x14000U & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U]))) 
            & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__operands_ready))) 
           & (0U != (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready)));
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_unit_stall 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_valid) 
             & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                   >> 7U))) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                  >> 0xeU))) & (~ (IData)(
                                                          (0U 
                                                           != (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_valid) 
            & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                  >> 0xeU))) & (0U != (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready)));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to 
        = ((- (IData)(((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_valid) 
                       & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                             >> 0xeU))))) & (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_stage_ready 
        = (1U & ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                     >> 0xcU)) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_valid) 
                                  & (0U != (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready)))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__oldest_fp_issued_fifo.potential_push 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
              >> 9U));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pre_issue_count_next 
        = (0xfU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pre_issue_count) 
                    + (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__pc_id_assigned)) 
                   - (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__post_issue_count_next 
        = (0xfU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__post_issue_count) 
                    + (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued)) 
                   - (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next) 
                            >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_instruction_issued_with_rd 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
              >> 8U));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall 
        = ((((vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
              >> 0xcU) & (0U == (0x14000U & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U]))) 
            & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_operands_ready))) 
           & (0U != (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready)));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_no_id_stall 
        = (((~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                >> 0xcU)) & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__inflight_count) 
                             >> 3U)) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                           >> 0xeU)));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_unit_stall 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_valid) 
             & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                >> 7U)) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                              >> 0xeU))) & (~ (IData)(
                                                      (0U 
                                                       != (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_ready)))));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_no_instruction_stall 
        = (1U & (((~ (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_no_id_stall)) 
                  & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                        >> 0xcU))) | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                      >> 0xeU)));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_other_stall 
        = (1U & ((((vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                    >> 7U) & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                              >> 0xcU)) & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued))) 
                 & (~ ((((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
                         | (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_unit_stall)) 
                        | (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_no_id_stall)) 
                       | (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_no_instruction_stall)))));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fls_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 1U)) & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                          >> 7U));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 7U)) & (4U == (7U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[0xaU])));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 7U)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_fadd));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 7U)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_fmul));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fdiv_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 8U)) & (0x68U == (0x3f8U & vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U])));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fsqrt_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 8U)) & (0x168U == (0x3f8U & vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U])));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fcmp_operand_stall 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
           & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
                >> 0xaU) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_fcmp_r)) 
              | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
                  >> 9U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_minmax_r))));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fsign_inject_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 9U)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_sign_inj_r));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fclass_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 0xaU)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_class_r));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fcvt_operand_stall 
        = (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall) 
            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
               >> 0xaU)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_f2i_r));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fls 
        = (((((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
               [2U] >> 4U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict)) 
             | ((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
                 [1U] >> 4U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict))) 
            | ((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
                [0U] >> 4U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict))) 
           & (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fmadd 
        = ((((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
              [2U] & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict)) 
             | (vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
                [1U] & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict))) 
            | (vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
               [0U] & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict))) 
           & (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fdiv_sqrt 
        = (((((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
               [2U] >> 1U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict)) 
             | ((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
                 [1U] >> 1U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict))) 
            | ((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
                [0U] >> 1U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict))) 
           & (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_wb2fp 
        = (((((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
               [2U] >> 2U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict)) 
             | ((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
                 [1U] >> 2U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict))) 
            | ((vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot
                [0U] >> 2U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict))) 
           & (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_stall_due_to_fmadd 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fmadd) 
           & (((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall) 
               | (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall)) 
              | (IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall)));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs1 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs2 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs3 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall_rs1 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall_rs2 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall_rs1 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall_rs2 
        = ((IData)(vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict));
    vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued_with_rd 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued) 
            & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                  >> 8U))) & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                              >> 0x13U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__new_request[0U] 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to) 
                 >> 7U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__new_request[1U] 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to) 
                 >> 8U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__new_request[2U] 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to) 
                 >> 9U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__new_request[3U] 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to) 
                 >> 0xaU));
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state 
        = vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state;
    if ((0U == vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 1U;
    } else if ((1U == vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 2U;
    } else if ((2U == vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state)) {
        if ((0x40U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state_counter))) {
            vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 3U;
        }
    } else if ((3U == vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state)) {
        if ((0x200U & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U])) {
            vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 6U;
        } else if ((1U & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to) 
                            >> 6U) | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__interrupt_pending)) 
                          | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                             >> 0xaU)))) {
            vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 5U;
        }
    } else if ((4U == vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state)) {
        if ((0x40U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state_counter))) {
            vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 3U;
        }
    } else if ((5U == vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state)) {
        if (((0U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__post_issue_count)) 
             & (~ (IData)((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid)))))) {
            vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 3U;
        } else if ((0x200U & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U])) {
            vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 6U;
        }
    } else if ((6U == vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state)) {
        if (((0U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__post_issue_count)) 
             & (~ (IData)((0U != ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid) 
                                  & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__released))))))) {
            vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 3U;
        }
    } else {
        vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 0U;
    }
    __Vtemp_h0faf1974__0[0U] = (((IData)((((QData)((IData)(
                                                           (7U 
                                                            & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                               >> 0x11U)))) 
                                           << 0x24U) 
                                          | (((QData)((IData)(
                                                              vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[3U])) 
                                              << 4U) 
                                             | (QData)((IData)(
                                                               ((0xeU 
                                                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                                    >> 0xeU)) 
                                                                | (1U 
                                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                      >> 0xdU)))))))) 
                                 << 5U) | ((0x1cU & 
                                            (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                             >> 8U)) 
                                           | ((0x1ffffeU 
                                               & (((vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                    >> 0xbU) 
                                                   & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage)) 
                                                  & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__1__KET__.ready) 
                                                     << 1U))) 
                                              | (1U 
                                                 & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to) 
                                                      >> 1U) 
                                                     & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unaligned_addr))) 
                                                    & (~ 
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                        >> 0xeU)))))));
    __Vtemp_h0faf1974__0[1U] = (((IData)((((QData)((IData)(
                                                           (7U 
                                                            & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                               >> 0x11U)))) 
                                           << 0x24U) 
                                          | (((QData)((IData)(
                                                              vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[3U])) 
                                              << 4U) 
                                             | (QData)((IData)(
                                                               ((0xeU 
                                                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                                    >> 0xeU)) 
                                                                | (1U 
                                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                      >> 0xdU)))))))) 
                                 >> 0x1bU) | (((IData)(
                                                       (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address)) 
                                                         << 6U) 
                                                        | (QData)((IData)(
                                                                          ((0x20U 
                                                                            & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                               >> 0xbU)) 
                                                                           | ((0x10U 
                                                                               & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                                >> 0xbU)) 
                                                                              | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be))))))) 
                                               << 0xcU) 
                                              | ((IData)(
                                                         ((((QData)((IData)(
                                                                            (7U 
                                                                             & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                                >> 0x11U)))) 
                                                            << 0x24U) 
                                                           | (((QData)((IData)(
                                                                               vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[3U])) 
                                                               << 4U) 
                                                              | (QData)((IData)(
                                                                                ((0xeU 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                                                >> 0xeU)) 
                                                                                | (1U 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                                >> 0xdU))))))) 
                                                          >> 0x20U)) 
                                                 << 5U)));
    __Vtemp_h0faf1974__0[2U] = (((0x1fU & ((IData)(
                                                   (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address)) 
                                                     << 6U) 
                                                    | (QData)((IData)(
                                                                      ((0x20U 
                                                                        & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                           >> 0xbU)) 
                                                                       | ((0x10U 
                                                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                              >> 0xbU)) 
                                                                          | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be))))))) 
                                           >> 0x14U)) 
                                 | ((IData)(((((QData)((IData)(
                                                               (7U 
                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                   >> 0x11U)))) 
                                               << 0x24U) 
                                              | (((QData)((IData)(
                                                                  vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[3U])) 
                                                  << 4U) 
                                                 | (QData)((IData)(
                                                                   ((0xeU 
                                                                     & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                                        >> 0xeU)) 
                                                                    | (1U 
                                                                       & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                          >> 0xdU))))))) 
                                             >> 0x20U)) 
                                    >> 0x1bU)) | ((0xfe0U 
                                                   & ((IData)(
                                                              (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address)) 
                                                                << 6U) 
                                                               | (QData)((IData)(
                                                                                ((0x20U 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                                >> 0xbU)) 
                                                                                | ((0x10U 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                                >> 0xbU)) 
                                                                                | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be))))))) 
                                                      >> 0x14U)) 
                                                  | ((IData)(
                                                             ((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address)) 
                                                                << 6U) 
                                                               | (QData)((IData)(
                                                                                ((0x20U 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                                >> 0xbU)) 
                                                                                | ((0x10U 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                                                >> 0xbU)) 
                                                                                | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be)))))) 
                                                              >> 0x20U)) 
                                                     << 0xcU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[0U] 
        = (((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U])) 
                      << 0x3fU) | (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[1U])) 
                                    << 0x1fU) | ((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[0U])) 
                                                 >> 1U)))) 
            << 1U) | (1U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address 
                            >> 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[1U] 
        = (((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U])) 
                      << 0x3fU) | (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[1U])) 
                                    << 0x1fU) | ((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[0U])) 
                                                 >> 1U)))) 
            >> 0x1fU) | ((IData)(((((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U])) 
                                    << 0x3fU) | (((QData)((IData)(
                                                                  vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[1U])) 
                                                  << 0x1fU) 
                                                 | ((QData)((IData)(
                                                                    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[0U])) 
                                                    >> 1U))) 
                                  >> 0x20U)) << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[2U] 
        = ((__Vtemp_h0faf1974__0[0U] << 3U) | ((4U 
                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
                                                   << 1U)) 
                                               | ((2U 
                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[0U] 
                                                      << 1U)) 
                                                  | ((IData)(
                                                             ((((QData)((IData)(
                                                                                vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U])) 
                                                                << 0x3fU) 
                                                               | (((QData)((IData)(
                                                                                vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[1U])) 
                                                                   << 0x1fU) 
                                                                  | ((QData)((IData)(
                                                                                vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[0U])) 
                                                                     >> 1U))) 
                                                              >> 0x20U)) 
                                                     >> 0x1fU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[3U] 
        = ((__Vtemp_h0faf1974__0[0U] >> 0x1dU) | (__Vtemp_h0faf1974__0[1U] 
                                                  << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[4U] 
        = ((__Vtemp_h0faf1974__0[1U] >> 0x1dU) | (__Vtemp_h0faf1974__0[2U] 
                                                  << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_advance 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
            >> 0xbU) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_stage_ready));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list.potential_push 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued_with_rd) 
           & (0U != (0x1fU & ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                               << 4U) | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                         >> 0x1cU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[0U] 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued_with_rd) 
            | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_instruction_issued_with_rd)) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
              >> 0x12U));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[1U] 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued_with_rd) 
             & (0U != (0x1fU & ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                 << 4U) | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                           >> 0x1cU))))) 
            & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                  >> 0x12U))) | (((IData)((0x81000U 
                                           == (0x81000U 
                                               & vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U]))) 
                                  & (0U != (0x1fU & 
                                            ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                              << 4U) 
                                             | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                >> 0x1cU))))) 
                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                    >> 0xeU)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_fifo.push 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[2U] 
                  >> 3U) & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[3U] 
                            >> 0x14U)));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_request 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[2U] 
                  >> 3U) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[3U] 
                               >> 0x13U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_sq_request 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[2U] 
                  >> 3U) & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry[3U] 
                            >> 0x13U)));
    if (vlSelf->taiga_sim__DOT__cpu__DOT__decode_advance) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_wb_group[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_rs_wb_group
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_wb_group[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_rs_wb_group
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__bypass[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__bypass[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_wb_group[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_rs_wb_group
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_wb_group[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_rs_wb_group
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_wb_group[2U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_rs_wb_group
            [2U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__bypass[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__bypass[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__bypass[2U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse
            [2U];
    } else {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_wb_group[0U] 
            = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.rs_wb_group
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_wb_group[1U] 
            = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.rs_wb_group
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__bypass[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse_r
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__bypass[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse_r
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_wb_group[0U] 
            = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.rs_wb_group
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_wb_group[1U] 
            = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.rs_wb_group
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_wb_group[2U] 
            = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.rs_wb_group
            [2U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__bypass[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse_r
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__bypass[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse_r
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__bypass[2U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse_r
            [2U];
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rename_valid 
        = (((~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                >> 0xeU)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_advance)) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
              >> 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rename_valid 
        = ((((~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                 >> 0xeU)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_advance)) 
            & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__uses_rd)) 
           & (0U != (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                              >> 0x13U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[0U] 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_advance) 
            & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
               >> 3U)) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                             >> 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[0U] 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_advance) 
             & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__uses_rd)) 
            & (0U != (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.phys_rd_addr))) 
           & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                 >> 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[3U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
            >> 0x12U) & vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts 
        = ((0xeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts)) 
           | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid) 
               & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__issued_one_hot))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash) 
                 == (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__hashes)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting 
        = ((0xeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting)) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts) 
              & (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_request)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed 
        = ((0xeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed)) 
           | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                       >> 2U)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_ack)));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0 
        = (7U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count) 
                  + (1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting))) 
                 - (1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next 
        = ((0xff8U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next)) 
           | (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts 
        = ((0xdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts)) 
           | (0xfffffffeU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid) 
                              & ((~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__issued_one_hot) 
                                     >> 1U)) << 1U)) 
                             & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash) 
                                 == (0xfU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__hashes) 
                                             >> 4U))) 
                                << 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting 
        = ((0xdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting)) 
           | (0xfffffffeU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts) 
                             & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_request) 
                                << 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed 
        = ((0xdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed)) 
           | (((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                        >> 3U)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_ack)) 
              << 1U));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0 
        = (7U & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count) 
                   >> 3U) + (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting) 
                                   >> 1U))) - (1U & 
                                               ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed) 
                                                >> 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next 
        = ((0xfc7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next)) 
           | ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0) 
              << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts 
        = ((0xbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts)) 
           | (0xfffffffcU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid) 
                              & ((~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__issued_one_hot) 
                                     >> 2U)) << 2U)) 
                             & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash) 
                                 == (0xfU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__hashes) 
                                             >> 8U))) 
                                << 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting 
        = ((0xbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting)) 
           | (0xfffffffcU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts) 
                             & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_request) 
                                << 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed 
        = ((0xbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed)) 
           | (((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                        >> 4U)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_ack)) 
              << 2U));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0 
        = (7U & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count) 
                   >> 6U) + (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting) 
                                   >> 2U))) - (1U & 
                                               ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed) 
                                                >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next 
        = ((0xe3fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next)) 
           | ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0) 
              << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts 
        = ((7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts)) 
           | (0xfffffff8U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid) 
                              & ((~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__issued_one_hot) 
                                     >> 3U)) << 3U)) 
                             & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash) 
                                 == (0xfU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__hashes) 
                                             >> 0xcU))) 
                                << 3U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting 
        = ((7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting)) 
           | (0xfffffff8U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts) 
                             & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_request) 
                                << 3U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed 
        = ((7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed)) 
           | (((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                        >> 5U)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_ack)) 
              << 3U));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0 
        = (7U & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count) 
                   >> 9U) + (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting) 
                                   >> 3U))) - (1U & 
                                               ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed) 
                                                >> 3U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next 
        = ((0x1ffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next)) 
           | ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h62b6d5f3__0) 
              << 9U));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index_next 
        = (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index) 
                 + (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_sq_request)));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index_one_hot = 0U;
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index_one_hot 
        = ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index_one_hot) 
           | (0xfU & ((IData)(1U) << (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_request_one_hot 
        = ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index_one_hot) 
           & (- (IData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_sq_request))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_update 
        = (1U & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rename_valid) 
                   | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rollback)) 
                  | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                     >> 0x12U)) | ((IData)((0x82U == 
                                            (0x82U 
                                             & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__retire)))) 
                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                      >> 0xdU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_update 
        = (1U & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rename_valid) 
                   | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rollback)) 
                  | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                     >> 0x12U)) | ((IData)((0x80U == 
                                            (0x82U 
                                             & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__retire)))) 
                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                      >> 0xdU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[3U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
            >> 0x12U) & vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [6U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[3U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
            >> 0x12U) & vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid_next 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid) 
            | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_request_one_hot)) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__issued_one_hot)));
}

VL_ATTR_COLD void Vtaiga_sim___024root___initial__TOP__0(Vtaiga_sim___024root* vlSelf);
VL_ATTR_COLD void Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf);

VL_ATTR_COLD void Vtaiga_sim___024root___eval_initial(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___eval_initial\n"); );
    // Body
    Vtaiga_sim___024root___initial__TOP__0(vlSelf);
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___initial__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index));
    vlSelf->__Vclklast__TOP__clk = vlSelf->clk;
}

VL_ATTR_COLD void Vtaiga_sim___024root___settle__TOP__0(Vtaiga_sim___024root* vlSelf);
void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf);
VL_ATTR_COLD void Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0(Vtaiga_sim_lfsr__W4* vlSelf);
VL_ATTR_COLD void Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0(Vtaiga_sim_lfsr__W4* vlSelf);
void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf);
void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf);
void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf);
void Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz__0(Vtaiga_sim_clz_tree* vlSelf);

VL_ATTR_COLD void Vtaiga_sim___024root___eval_settle(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___eval_settle\n"); );
    // Body
    Vtaiga_sim___024root___settle__TOP__0(vlSelf);
    Vtaiga_sim___024root___settle__TOP__1(vlSelf);
    Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz__0((&vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__genblk3__DOT__frac_clz));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_write_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_lfsr__W4___settle__TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index__0((&vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index));
    Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz__0((&vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__genblk3__DOT__frac_clz));
    Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz__0((&vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__genblk1__DOT__frac_clz));
    Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz__0((&vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__genblk1__DOT__frac_clz));
    Vtaiga_sim_clz_tree___sequent__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz__0((&vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__genblk2__DOT__frac_clz));
    Vtaiga_sim___024root___settle__TOP__2(vlSelf);
}
