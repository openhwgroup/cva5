// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim__Syms.h"
#include "Vtaiga_sim___024root.h"

extern const VlUnpacked<QData/*63:0*/, 256> Vtaiga_sim__ConstPool__TABLE_h95de7929_0;
extern const VlUnpacked<CData/*0:0*/, 256> Vtaiga_sim__ConstPool__TABLE_hbdb5e6c2_0;
extern const VlWide<9>/*287:0*/ Vtaiga_sim__ConstPool__CONST_h5285fb67_0;
extern const VlUnpacked<CData/*1:0*/, 256> Vtaiga_sim__ConstPool__TABLE_he47736a6_0;

VL_ATTR_COLD void Vtaiga_sim___024root___settle__TOP__0(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___settle__TOP__0\n"); );
    // Init
    CData/*0:0*/ taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    CData/*0:0*/ taiga_sim__DOT____Vlvbound_hb000006e__0;
    VlWide<3>/*68:0*/ taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs;
    CData/*0:0*/ taiga_sim__DOT__l2_to_mem__DOT__amo_unit__DOT__rs1_smaller_than_rs2;
    QData/*34:0*/ taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
    VlWide<3>/*66:0*/ taiga_sim__DOT__cpu__DOT__div_inputs;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fetch_block__DOT__is_branch_or_jump;
    CData/*4:0*/ taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex;
    CData/*3:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot;
    SData/*13:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_decode;
    CData/*6:0*/ taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT____Vlvbound_h84bfe905__0;
    CData/*3:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot;
    IData/*20:0*/ taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_decode;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_csr;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__mult_div_op;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__carry_in;
    QData/*32:0*/ taiga_sim__DOT__cpu__DOT__alu_unit_block__DOT__add_sub_result;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_muxed_load_data;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellout__sub_unit_select__int_out;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected;
    CData/*3:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest_one_hot;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment;
    QData/*42:0*/ taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__writeback_block__DOT____Vlvbound_h84ca567e__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_hcae1b096__0;
    CData/*2:0*/ taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_hcd32a4c9__0;
    QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_h841830c4__0;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_h41f75b63__0;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x_overflow;
    SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt_swapped;
    SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt_swapped;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_hidden_bit_pre_normalized_swapped;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_hidden_bit_pre_normalized_swapped;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap;
    VlWide<9>/*268:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs;
    SData/*12:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo_intermediate;
    QData/*51:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__residual_bits;
    SData/*12:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__expo_diff;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs2_sign;
    SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs1_expo;
    VlWide<5>/*159:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1;
    VlWide<5>/*159:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_zero;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__invalid_operation;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__early_terminate;
    SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__expo_normalized;
    CData/*5:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__radicand_clz;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__i;
    QData/*55:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__subtraction;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_by_zero;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__right_shift;
    SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo;
    QData/*52:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac;
    IData/*31:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__special_case_result;
    QData/*63:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_if_overflow;
    SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shift_amt;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__right_shift;
    VlWide<5>/*158:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shifter_in;
    VlWide<5>/*158:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result;
    VlWide<5>/*158:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed;
    QData/*51:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_norm;
    VlWide<4>/*103:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vcellout__round__roundup;
    QData/*51:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_out;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__overflowExp;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__underflowExp;
    SData/*10:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_overflow_norm;
    SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm_right_shift;
    SData/*11:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm_left_shift;
    CData/*0:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_less_than_left_shift_amt;
    VlWide<5>/*158:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left;
    VlWide<5>/*158:0*/ taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right;
    CData/*0:0*/ __Vfunc_address_range_check__1__Vfuncout;
    IData/*31:0*/ __Vfunc_address_range_check__1__addr;
    IData/*16:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__3__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__3__pc;
    IData/*16:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__4__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__4__pc;
    IData/*16:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__5__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__5__pc;
    CData/*0:0*/ __Vfunc_address_range_check__6__Vfuncout;
    IData/*31:0*/ __Vfunc_address_range_check__6__addr;
    CData/*0:0*/ __Vfunc_address_range_check__7__Vfuncout;
    IData/*31:0*/ __Vfunc_address_range_check__7__addr;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__8__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__9__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__10__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__11__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__12__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__13__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__14__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__15__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__16__Vfuncout;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__17__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__a;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__b;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__a;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__b;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__a;
    CData/*0:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__b;
    VlWide<5>/*158:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__in;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i;
    VlWide<5>/*158:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__in;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i;
    CData/*7:0*/ __Vtableidx1;
    CData/*7:0*/ __Vtableidx2;
    CData/*7:0*/ __Vtableidx3;
    SData/*14:0*/ TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface__DOT__rs_addr;
    IData/*31:0*/ TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET____DOT__rd;
    VlWide<5>/*159:0*/ __Vtemp_hfa3ab7a8__0;
    VlWide<3>/*95:0*/ __Vtemp_h041f2230__0;
    VlWide<7>/*223:0*/ __Vtemp_ha7602ea7__0;
    VlWide<7>/*223:0*/ __Vtemp_hf5cbfb1a__0;
    VlWide<10>/*319:0*/ __Vtemp_heeb462dd__0;
    VlWide<3>/*95:0*/ __Vtemp_hf3c0533d__0;
    VlWide<3>/*95:0*/ __Vtemp_h94d9bf51__0;
    VlWide<3>/*95:0*/ __Vtemp_hf7c80da1__0;
    VlWide<5>/*159:0*/ __Vtemp_hf725ef03__0;
    VlWide<5>/*159:0*/ __Vtemp_h8f86743b__0;
    VlWide<5>/*159:0*/ __Vtemp_hb4d0d369__0;
    VlWide<5>/*159:0*/ __Vtemp_hf39bef00__0;
    VlWide<5>/*159:0*/ __Vtemp_hb50f37c1__0;
    VlWide<3>/*95:0*/ __Vtemp_h30e72d2b__0;
    VlWide<3>/*95:0*/ __Vtemp_hef1d8ee0__0;
    VlWide<5>/*159:0*/ __Vtemp_hfa356fe8__0;
    VlWide<5>/*159:0*/ __Vtemp_h4472ca76__0;
    VlWide<6>/*191:0*/ __Vtemp_h4a9d8ffe__0;
    VlWide<6>/*191:0*/ __Vtemp_h7a991c01__0;
    VlWide<6>/*191:0*/ __Vtemp_h558c6d26__0;
    VlWide<6>/*191:0*/ __Vtemp_h4a9d8ffe__1;
    VlWide<6>/*191:0*/ __Vtemp_h7a991c01__1;
    VlWide<6>/*191:0*/ __Vtemp_h4edd94c7__0;
    VlWide<6>/*191:0*/ __Vtemp_h4a9d8ffe__2;
    VlWide<6>/*191:0*/ __Vtemp_h7a991c01__2;
    VlWide<6>/*191:0*/ __Vtemp_h6d43b682__0;
    // Body
    vlSelf->instruction_bram_be = 0U;
    vlSelf->instruction_bram_data_in = 0U;
    vlSelf->ddr_axi_arburst = 1U;
    vlSelf->ddr_axi_arcache = 3U;
    vlSelf->ddr_axi_arsize = 2U;
    vlSelf->ddr_axi_awburst = 1U;
    vlSelf->ddr_axi_awcache = 3U;
    vlSelf->ddr_axi_bready = 1U;
    vlSelf->ddr_axi_rready = 1U;
    vlSelf->ddr_axi_awid = vlSelf->taiga_sim__DOT__axi_awid;
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[0U][0U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__0__KET__.fflags;
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[1U][0U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__1__KET__.fflags;
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[1U][1U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__2__KET__.fflags;
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[1U][2U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__3__KET__.fflags;
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[1U][3U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET__.fflags;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_ready 
        = (1U | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_ready));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry[0U] 
        = (0xdU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry
           [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry[0U] 
        = ((0xbU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__2__KET__.carry) 
                     << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe[0U] 
        = ((0xbU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__2__KET__.safe) 
                     << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal[0U] 
        = ((7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.subnormal) 
                     << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift[0U] 
        = ((7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.right_shift) 
                     << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt[0U] 
        = ((0x1ffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt
            [0U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.right_shift_amt)) 
                     << 0x21U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow[0U] 
        = ((7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.expo_overflow) 
                     << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U] 
        = (0xfffff7ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U] 
        = (0xfffffcffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U] 
        = (0xffffff00U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_fflags[0U][0U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_unit_wb__BRA__0__KET__.fflags;
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel[0U] 
        = (6U & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
           [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__unit_data_array[0U] 
        = vlSelf->instruction_bram_data_out;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array[0U] 
        = vlSelf->data_bram_data_out;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[3U] 
        = (0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux
           [3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[0U] 
        = (0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux
           [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[3U] 
        = (0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux
           [3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry 
        = (0x400000U | vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[0U] 
        = ((0x1fffULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [0U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__0__KET__.addr)) 
                     << 0xdU));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[0U] 
        = ((0x7ffffffe1ffULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [0U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__0__KET__.be)) 
                     << 9U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[0U] 
        = ((0x7fffffffeffULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [0U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__0__KET__.rnw)) 
                     << 8U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[0U] 
        = ((0x7ffffffff7fULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [0U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__0__KET__.is_amo)) 
                     << 7U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[0U] 
        = ((0x7ffffffff83ULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [0U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__0__KET__.amo_type_or_burst_size)) 
                     << 2U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[0U] 
        = ((0x7fffffffffcULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [0U]) | (IData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__0__KET__.sub_id)));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[1U] 
        = ((0x1fffULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [1U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__1__KET__.addr)) 
                     << 0xdU));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[1U] 
        = ((0x7ffffffe1ffULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [1U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__1__KET__.be)) 
                     << 9U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[1U] 
        = ((0x7fffffffeffULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [1U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__1__KET__.rnw)) 
                     << 8U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[1U] 
        = ((0x7ffffffff7fULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [1U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__1__KET__.is_amo)) 
                     << 7U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[1U] 
        = ((0x7ffffffff83ULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [1U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__1__KET__.amo_type_or_burst_size)) 
                     << 2U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[1U] 
        = ((0x7fffffffffcULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in
            [1U]) | (IData)((IData)(vlSymsp->TOP__taiga_sim__DOT__l2__BRA__1__KET__.sub_id)));
    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
        = (0xfffffc03U & vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U]);
    vlSelf->ddr_axi_awvalid = vlSelf->taiga_sim__DOT__axi_awvalid;
    vlSelf->instruction_pc_dec = ((vlSelf->taiga_sim__DOT__tr[2U] 
                                   << 6U) | (vlSelf->taiga_sim__DOT__tr[1U] 
                                             >> 0x1aU));
    vlSelf->instruction_data_dec = ((vlSelf->taiga_sim__DOT__tr[1U] 
                                     << 6U) | (vlSelf->taiga_sim__DOT__tr[0U] 
                                               >> 0x1aU));
    vlSelf->instruction_issued = (1U & (vlSelf->taiga_sim__DOT__tr[0U] 
                                        >> 0x13U));
    vlSelf->LargeSigTrace[0U] = (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                 >> 0x1fU);
    vlSelf->LargeSigTrace[1U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x1eU));
    vlSelf->LargeSigTrace[2U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x1dU));
    vlSelf->LargeSigTrace[3U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x1cU));
    vlSelf->LargeSigTrace[4U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x1bU));
    vlSelf->LargeSigTrace[5U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x1aU));
    vlSelf->LargeSigTrace[6U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x19U));
    vlSelf->LargeSigTrace[7U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x18U));
    vlSelf->LargeSigTrace[8U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x17U));
    vlSelf->LargeSigTrace[9U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                       >> 0x16U));
    vlSelf->LargeSigTrace[0xaU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                         >> 0x15U));
    vlSelf->LargeSigTrace[0xbU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                         >> 0x14U));
    vlSelf->LargeSigTrace[0xcU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                         >> 0x13U));
    vlSelf->LargeSigTrace[0xdU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                         >> 0x12U));
    vlSelf->LargeSigTrace[0xeU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                         >> 0x11U));
    vlSelf->LargeSigTrace[0xfU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                         >> 0x10U));
    vlSelf->LargeSigTrace[0x10U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 0xfU));
    vlSelf->LargeSigTrace[0x11U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 0xeU));
    vlSelf->LargeSigTrace[0x12U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 0xdU));
    vlSelf->LargeSigTrace[0x13U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 0xcU));
    vlSelf->LargeSigTrace[0x14U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 0xbU));
    vlSelf->LargeSigTrace[0x15U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 0xaU));
    vlSelf->LargeSigTrace[0x16U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 9U));
    vlSelf->LargeSigTrace[0x17U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 8U));
    vlSelf->LargeSigTrace[0x18U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 7U));
    vlSelf->LargeSigTrace[0x19U] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 6U));
    vlSelf->LargeSigTrace[0x1aU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 5U));
    vlSelf->LargeSigTrace[0x1bU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 4U));
    vlSelf->LargeSigTrace[0x1cU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 3U));
    vlSelf->LargeSigTrace[0x1dU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 2U));
    vlSelf->LargeSigTrace[0x1eU] = (1U & (vlSelf->taiga_sim__DOT__fp_tr[0U] 
                                          >> 1U));
    vlSelf->LargeSigTrace[0x1fU] = (1U & vlSelf->taiga_sim__DOT__fp_tr[0U]);
    vlSelf->store_queue_empty = (1U & (~ (IData)((0U 
                                                  != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid)))));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata_fifo.pop 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__inflight_count) 
                 >> 4U));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__1__KET__.pop 
        = vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__returndata_fifos__BRA__1__KET__.valid;
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__1__KET__.valid 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__inflight_count) 
                 >> 4U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list.pop 
        = (IData)((0x80U == (0x82U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__retire))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list.pop 
        = (IData)((0x82U == (0x82U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__retire))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__next_rad 
        = (0xfffffffffffffcULL & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__rad 
                                  << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_next 
        = (0x1eU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_next));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT____Vcellinp__in_progress_m__set 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.valid) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__in_progress)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT____Vcellinp__in_progress_m__set 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo.valid) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__running)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__new_PR 
        = (0xffffffffffffffULL & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__PR 
                                  - vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__divisor_r));
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x19U));
    vlSelf->taiga_events[0U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x18U));
    vlSelf->taiga_events[1U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x17U));
    vlSelf->taiga_events[2U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x16U));
    vlSelf->taiga_events[3U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x15U));
    vlSelf->taiga_events[4U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x14U));
    vlSelf->taiga_events[5U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x13U));
    vlSelf->taiga_events[6U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x12U));
    vlSelf->taiga_events[7U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x11U));
    vlSelf->taiga_events[8U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0x10U));
    vlSelf->taiga_events[9U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0xfU));
    vlSelf->taiga_events[0xaU] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0xeU));
    vlSelf->taiga_events[0xbU] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0xdU));
    vlSelf->taiga_events[0xcU] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0xcU));
    vlSelf->taiga_events[0xdU] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0xbU));
    vlSelf->taiga_events[0xeU] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 0xaU));
    vlSelf->taiga_events[0xfU] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 9U));
    vlSelf->taiga_events[0x10U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 8U));
    vlSelf->taiga_events[0x11U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 7U));
    vlSelf->taiga_events[0x12U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 6U));
    vlSelf->taiga_events[0x13U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 5U));
    vlSelf->taiga_events[0x14U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 4U));
    vlSelf->taiga_events[0x15U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 3U));
    vlSelf->taiga_events[0x16U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 2U));
    vlSelf->taiga_events[0x17U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__tr[0U] 
                                                >> 1U));
    vlSelf->taiga_events[0x18U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_h5f85fc50__0 = (1U & 
                                               vlSelf->taiga_sim__DOT__tr[0U]);
    vlSelf->taiga_events[0x19U] = taiga_sim__DOT____Vlvbound_h5f85fc50__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0x14U));
    vlSelf->fp_taiga_events[0U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0x13U));
    vlSelf->fp_taiga_events[1U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0x12U));
    vlSelf->fp_taiga_events[2U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0x11U));
    vlSelf->fp_taiga_events[3U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0x10U));
    vlSelf->fp_taiga_events[4U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0xfU));
    vlSelf->fp_taiga_events[5U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0xeU));
    vlSelf->fp_taiga_events[6U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0xdU));
    vlSelf->fp_taiga_events[7U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0xcU));
    vlSelf->fp_taiga_events[8U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0xbU));
    vlSelf->fp_taiga_events[9U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 0xaU));
    vlSelf->fp_taiga_events[0xaU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 9U));
    vlSelf->fp_taiga_events[0xbU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 8U));
    vlSelf->fp_taiga_events[0xcU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 7U));
    vlSelf->fp_taiga_events[0xdU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 6U));
    vlSelf->fp_taiga_events[0xeU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 5U));
    vlSelf->fp_taiga_events[0xfU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 4U));
    vlSelf->fp_taiga_events[0x10U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 3U));
    vlSelf->fp_taiga_events[0x11U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 2U));
    vlSelf->fp_taiga_events[0x12U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[2U] 
                                                >> 1U));
    vlSelf->fp_taiga_events[0x13U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               vlSelf->taiga_sim__DOT__fp_tr[2U]);
    vlSelf->fp_taiga_events[0x14U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                               >> 0x1fU);
    vlSelf->fp_taiga_events[0x15U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x1eU));
    vlSelf->fp_taiga_events[0x16U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x1dU));
    vlSelf->fp_taiga_events[0x17U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x1cU));
    vlSelf->fp_taiga_events[0x18U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x1bU));
    vlSelf->fp_taiga_events[0x19U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x1aU));
    vlSelf->fp_taiga_events[0x1aU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x19U));
    vlSelf->fp_taiga_events[0x1bU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x18U));
    vlSelf->fp_taiga_events[0x1cU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x17U));
    vlSelf->fp_taiga_events[0x1dU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x16U));
    vlSelf->fp_taiga_events[0x1eU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x15U));
    vlSelf->fp_taiga_events[0x1fU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x14U));
    vlSelf->fp_taiga_events[0x20U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x13U));
    vlSelf->fp_taiga_events[0x21U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x12U));
    vlSelf->fp_taiga_events[0x22U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x11U));
    vlSelf->fp_taiga_events[0x23U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0x10U));
    vlSelf->fp_taiga_events[0x24U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0xfU));
    vlSelf->fp_taiga_events[0x25U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0xeU));
    vlSelf->fp_taiga_events[0x26U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0xdU));
    vlSelf->fp_taiga_events[0x27U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0xcU));
    vlSelf->fp_taiga_events[0x28U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0xbU));
    vlSelf->fp_taiga_events[0x29U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 0xaU));
    vlSelf->fp_taiga_events[0x2aU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 9U));
    vlSelf->fp_taiga_events[0x2bU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 8U));
    vlSelf->fp_taiga_events[0x2cU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 7U));
    vlSelf->fp_taiga_events[0x2dU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 6U));
    vlSelf->fp_taiga_events[0x2eU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 5U));
    vlSelf->fp_taiga_events[0x2fU] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 4U));
    vlSelf->fp_taiga_events[0x30U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 3U));
    vlSelf->fp_taiga_events[0x31U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 2U));
    vlSelf->fp_taiga_events[0x32U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               (vlSelf->taiga_sim__DOT__fp_tr[1U] 
                                                >> 1U));
    vlSelf->fp_taiga_events[0x33U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    taiga_sim__DOT____Vlvbound_hb000006e__0 = (1U & 
                                               vlSelf->taiga_sim__DOT__fp_tr[1U]);
    vlSelf->fp_taiga_events[0x34U] = taiga_sim__DOT____Vlvbound_hb000006e__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_inputs = (
                                                   (0x3fULL 
                                                    & vlSelf->taiga_sim__DOT__cpu__DOT__gc_inputs) 
                                                   | (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu)) 
                                                       << 9U) 
                                                      | ((QData)((IData)(
                                                                         (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_ifence_r) 
                                                                           << 2U) 
                                                                          | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_mret_r) 
                                                                              << 1U) 
                                                                             | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_sret_r))))) 
                                                         << 6U)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__subtraction 
        = (0xffffffffffffffULL & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__current_subtractend 
                                  - (1ULL | (0xfffffffffffffcULL 
                                             & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt.quotient 
                                                << 2U)))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.rs_wb_group[0U] 
        = (1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_rs_wb_group));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.rs_wb_group[1U] 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_rs_wb_group) 
                 >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
        = ((0x1ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U]) 
           | ((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_int_rs1)) 
                        << 2U) | (QData)((IData)((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_zero) 
                                                   << 1U) 
                                                  | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_sign)))))) 
              << 9U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[5U] 
        = (0x7ffU & (((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_int_rs1)) 
                                << 2U) | (QData)((IData)(
                                                         (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_zero) 
                                                           << 1U) 
                                                          | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_sign)))))) 
                      >> 0x17U) | ((IData)(((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_int_rs1)) 
                                              << 2U) 
                                             | (QData)((IData)(
                                                               (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_zero) 
                                                                 << 1U) 
                                                                | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_sign))))) 
                                            >> 0x20U)) 
                                   << 9U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[0U] 
        = ((0xffffffc0U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[0U]) 
           | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_i2f) 
               << 5U) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_minmax) 
                          << 4U) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_sign_inj) 
                                     << 3U) | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[0U] 
        = ((0x7fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[0U]) 
           | ((IData)(((1U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))
                        ? (((QData)((IData)((1U & (~ (IData)(
                                                             (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                              >> 0x3fU)))))) 
                            << 0x3fU) | (0x7fffffffffffffffULL 
                                         & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))
                        : ((2U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))
                            ? (((QData)((IData)(((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                  ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                                 >> 0x3fU))) 
                                << 0x3fU) | (0x7fffffffffffffffULL 
                                             & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))
                            : (((QData)((IData)((1U 
                                                 & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                            >> 0x3fU))))) 
                                << 0x3fU) | (0x7fffffffffffffffULL 
                                             & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))))) 
              << 7U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[1U] 
        = (((IData)(((1U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))
                      ? (((QData)((IData)((1U & (~ (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                            >> 0x3fU)))))) 
                          << 0x3fU) | (0x7fffffffffffffffULL 
                                       & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))
                      : ((2U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))
                          ? (((QData)((IData)(((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                               >> 0x3fU))) 
                              << 0x3fU) | (0x7fffffffffffffffULL 
                                           & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))
                          : (((QData)((IData)((1U & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                             >> 0x3fU))))) 
                              << 0x3fU) | (0x7fffffffffffffffULL 
                                           & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))))) 
            >> 0x19U) | ((IData)((((1U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))
                                    ? (((QData)((IData)(
                                                        (1U 
                                                         & (~ (IData)(
                                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                                       >> 0x3fU)))))) 
                                        << 0x3fU) | 
                                       (0x7fffffffffffffffULL 
                                        & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))
                                    : ((2U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))
                                        ? (((QData)((IData)(
                                                            ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                              ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                                             >> 0x3fU))) 
                                            << 0x3fU) 
                                           | (0x7fffffffffffffffULL 
                                              & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))
                                        : (((QData)((IData)(
                                                            (1U 
                                                             & (IData)(
                                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                                        >> 0x3fU))))) 
                                            << 0x3fU) 
                                           | (0x7fffffffffffffffULL 
                                              & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1)))) 
                                  >> 0x20U)) << 7U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[2U] 
        = ((0xffffff80U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[2U]) 
           | ((IData)((((1U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))
                         ? (((QData)((IData)((1U & 
                                              (~ (IData)(
                                                         (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                          >> 0x3fU)))))) 
                             << 0x3fU) | (0x7fffffffffffffffULL 
                                          & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))
                         : ((2U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))
                             ? (((QData)((IData)(((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                   ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                                  >> 0x3fU))) 
                                 << 0x3fU) | (0x7fffffffffffffffULL 
                                              & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))
                             : (((QData)((IData)((1U 
                                                  & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                             >> 0x3fU))))) 
                                 << 0x3fU) | (0x7fffffffffffffffULL 
                                              & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1)))) 
                       >> 0x20U)) >> 0x19U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[0U] 
        = ((0xffffffbfU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[0U]) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_hidden_bit_pre_normalized) 
              << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x 
        = (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div.remainder 
           - (vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__shifted_divisor 
              << 1U));
    taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x_overflow 
        = (1U & (IData)((1ULL & (((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div.remainder)) 
                                  - ((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__shifted_divisor)) 
                                     << 1U)) >> 0x21U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm_right_shift 
        = (0xfffU & ((((0x800U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                                  >> 1U)) | (0x7ffU 
                                             & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                                                >> 1U))) 
                      & (- (IData)((1U & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                             >> 0xdU)))))) 
                     + (0x7ffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                   >> 1U) & (- (IData)(
                                                       (1U 
                                                        & (~ 
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                                            >> 0xdU)))))))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.rs_wb_group[0U] 
        = (1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_issue_rs_wb_group));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.rs_wb_group[1U] 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_issue_rs_wb_group) 
                 >> 1U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.rs_wb_group[2U] 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_issue_rs_wb_group) 
                 >> 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__predicted_pc 
        = (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk2__DOT__branch_table_banks__BRA__1__KET____DOT__addr_table__read_data)) 
            << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk2__DOT__branch_table_banks__BRA__0__KET____DOT__addr_table__read_data)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_less_than_left_shift_amt 
        = (1U & (((((0x800U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                               >> 1U)) | (0x7ffU & 
                                          (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                                           >> 1U))) 
                   & (- (IData)((1U & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                          >> 0xdU)))))) 
                  - (0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                               >> 0xeU))) >> 0xcU));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.requests 
        = ((2U & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__inflight_count) 
                  >> 3U)) | (1U & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__inflight_count) 
                                   >> 4U)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__right_shift 
        = (1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                 >> 0xbU));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shift_amt 
        = (0x7ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U]);
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shifter_in[0U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[1U] 
            << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[0U] 
                         >> 1U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shifter_in[1U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[2U] 
            << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[1U] 
                         >> 1U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shifter_in[2U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[3U] 
            << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[2U] 
                         >> 1U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shifter_in[3U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[4U] 
            << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[3U] 
                         >> 1U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shifter_in[4U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[4U] 
           >> 1U);
    VL_SHIFTRS_WWI(159,159,11, __Vtemp_hfa3ab7a8__0, taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shifter_in, (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__shift_amt));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[0U] 
        = __Vtemp_hfa3ab7a8__0[0U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[1U] 
        = __Vtemp_hfa3ab7a8__0[1U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[2U] 
        = __Vtemp_hfa3ab7a8__0[2U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[3U] 
        = __Vtemp_hfa3ab7a8__0[3U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[4U] 
        = (0x7fffffffU & __Vtemp_hfa3ab7a8__0[4U]);
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__in[0U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[0U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__in[1U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[1U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__in[2U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[2U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__in[3U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[3U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__in[4U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[4U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i = 0x9eU;
    while (VL_LTES_III(32, 0U, __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vlvbound_he380f72e__0 
            = ((0x9eU >= (0xffU & ((IData)(0x9eU) - __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i))) 
               & (__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__in[
                  (7U & (((IData)(0x9eU) - __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i) 
                         >> 5U))] >> (0x1fU & ((IData)(0x9eU) 
                                               - __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i))));
        if (VL_LIKELY((0x9eU >= (0xffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i)))) {
            vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout[(7U 
                                                                                & (__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i 
                                                                                >> 5U))] 
                = (((~ ((IData)(1U) << (0x1fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i))) 
                    & vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout[
                    (7U & (__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i 
                           >> 5U))]) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vlvbound_he380f72e__0) 
                                        << (0x1fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i)));
        }
        __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i 
            = (__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__unnamedblk1__DOT__i 
               - (IData)(1U));
    }
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[0U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout[0U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[1U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout[1U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[2U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout[2U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[3U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout[3U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[4U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout[4U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_norm 
        = (1U & (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__right_shift)
                   ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[4U]
                   : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[4U]) 
                 >> 0x1cU));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm 
        = (0xfffffffffffffULL & (((QData)((IData)(((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__right_shift)
                                                    ? 
                                                   taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[4U]
                                                    : 
                                                   taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[4U]))) 
                                  << 0x18U) | ((QData)((IData)(
                                                               ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__right_shift)
                                                                 ? 
                                                                taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[3U]
                                                                 : 
                                                                taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[3U]))) 
                                               >> 8U)));
    if (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__right_shift) {
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[0U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[0U];
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[1U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[1U];
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[2U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[2U];
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[3U] 
            = (0xffU & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result[3U]);
    } else {
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[0U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[0U];
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[1U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[1U];
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[2U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[2U];
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[3U] 
            = (0xffU & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_reversed[3U]);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__uses_rd_table
            [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next
            [1U]] << 1U) | vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__uses_rd_table
           [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next
           [0U]]);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_output_valid 
        = (1U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid) 
                  & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__released)) 
                 >> (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest)));
    vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__retire_ids
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__retire_ids
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_ready 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_ready)) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT__ready) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__retire_ids_next[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__retire_ids_next[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__retire_port_valid[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__retire_port_valid
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__retire_port_valid[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__retire_port_valid
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry 
        = (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk1__DOT__branch_tag_banks__BRA__1__KET____DOT__tag_bank__read_data)) 
            << 0x17U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk1__DOT__branch_tag_banks__BRA__0__KET____DOT__tag_bank__read_data)));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr 
        = vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_attr
        [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest];
    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[3U] 
        = (IData)((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                    [0U])) << 0x20U) 
                   | (QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                     [1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[4U] 
        = (IData)(((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                     [0U])) << 0x20U) 
                    | (QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                      [1U]))) >> 0x20U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo.pop 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo.valid) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__running)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id[0U] 
        = ((0xff8U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id
            [0U]) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id
           [1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id[0U] 
        = ((0xfc7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id
            [0U]) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id
                     [2U] << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id[0U] 
        = ((0x1ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.id) 
                     << 9U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm[0U] 
        = ((0x1ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.rm) 
                     << 9U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][9U] 
        = ((0xffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
            [0U][9U]) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.grs[0U] 
                         << 0x18U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][0xaU] 
        = ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.grs[0U] 
            >> 8U) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.grs[1U] 
                      << 0x18U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][0xbU] 
        = ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.grs[1U] 
            >> 8U) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.grs[2U] 
                      << 0x18U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][0xcU] 
        = ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.grs[2U] 
            >> 8U) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.grs[3U] 
                      << 0x18U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry[0U] 
        = ((7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.carry) 
                     << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe[0U] 
        = ((7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.safe) 
                     << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden[0U] 
        = ((7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.hidden) 
                     << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz[0U] 
        = ((0x1ffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz
            [0U]) | ((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.clz)) 
                     << 0x21U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd[0U][3U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.rd;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_fflags[0U][3U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.fflags;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id[0U] 
        = ((0xe3fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id
            [0U]) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                      [0U] ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__id_in_progress)
                       : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__in_progress_attr)) 
                     << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm[0U] 
        = ((0xe3fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm
            [0U]) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                      [0U] ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rm)
                       : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rm)) 
                     << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo 
        = (0xfffU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo_r) 
                      - (1U & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo_r)))) 
                     - (IData)(0x3ffU)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__residual_bits 
        = (0xfffffffffffffULL & (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac_intermediate[1U])) 
                                  << 0x20U) | (QData)((IData)(
                                                              vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac_intermediate[0U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs[0U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__residual_bits;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__grs[0U] 
        = (7U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt.quotient));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__result_frac[0U] 
        = (0x1fffffffffffffULL & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt.quotient 
                                  >> 3U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_by_zero 
        = (((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_zero)) 
            & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_inf))) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_zero));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_QNaN 
        = (((((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_zero) 
                & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_zero)) 
               | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_inf) 
                  & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_inf))) 
              | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_SNaN)) 
             | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_SNaN)) 
            | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_QNaN)) 
           | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_QNaN));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U] 
        = ((0xffffefffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U]) 
           | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
              [0U] << 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U] 
        = ((0xfffffbffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U]) 
           | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
              [1U] << 0xaU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U] 
        = ((0x1fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U]) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2) 
              << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[5U] 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2) 
            >> 0x13U) | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                  >> 0x20U)) << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[6U] 
        = (((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                     >> 0x20U)) >> 0x13U) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                             << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[7U] 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
            >> 0x13U) | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                  >> 0x20U)) << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[8U] 
        = ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                    >> 0x20U)) >> 0x13U);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U] 
        = ((0xfff000ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U]) 
           | (((0x800U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_expo_diff))
                ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_expo_diff_negate)
                : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_expo_diff)) 
              << 8U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U] 
        = ((0x3fffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U]) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_fn7) 
              << 0x1eU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U] 
        = ((0xffffff00U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U]) 
           | (0x3fffffffU & ((0x3fffffe0U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                             << 5U)) 
                             | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_fn7) 
                                >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U] 
        = ((0xffcfffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U]) 
           | (0xfff00000U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_swap) 
                              << 0x15U) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_add) 
                                           << 0x14U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U] 
        = ((0xc03fffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U]) 
           | (0xffc00000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                               [0U] << 0x1dU) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                  [0U] 
                                                  << 0x1cU) 
                                                 | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                     [0U] 
                                                     << 0x1bU) 
                                                    | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                       [0U] 
                                                       << 0x1aU)))) 
                             | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                 [1U] << 0x19U) | (
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                    [1U] 
                                                    << 0x18U) 
                                                   | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                       [1U] 
                                                       << 0x17U) 
                                                      | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                         [1U] 
                                                         << 0x16U)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized 
        = (((QData)((IData)((0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                               >> 0x34U))))) 
            << 0x34U) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_frac_pre_normalized);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized 
        = (((QData)((IData)((0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                               >> 0x34U))))) 
            << 0x34U) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_frac_pre_normalized);
    if (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_swap) {
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_pre_normalize_shift_amt;
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_pre_normalize_shift_amt;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
            [0U];
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_hidden_bit_pre_normalized_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_hidden_bit_pre_normalized;
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_hidden_bit_pre_normalized_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_hidden_bit_pre_normalized;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized;
    } else {
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_pre_normalize_shift_amt;
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_pre_normalize_shift_amt;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
            [1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped[0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
            [0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped[1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
            [1U];
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_hidden_bit_pre_normalized_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_hidden_bit_pre_normalized;
        taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_hidden_bit_pre_normalized_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_hidden_bit_pre_normalized;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized;
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next
        [1U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list.data_out 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__lut_ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__read_index];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac[0U] 
        = (0x3fffffffffffffULL & (((QData)((IData)(
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac_intermediate[3U])) 
                                   << 0x2cU) | (((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac_intermediate[2U])) 
                                                 << 0xcU) 
                                                | ((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac_intermediate[1U])) 
                                                   >> 0x14U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id[1U] 
        = ((0x3ffc7U & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id
            [1U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__2__KET__.id) 
                     << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id[1U] 
        = ((0x3fe3fU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id
            [1U]) | (vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__id
                     [1U] << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id[1U] 
        = ((0x3f1ffU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id
            [1U]) | (0xe00U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress_attr) 
                               << 9U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id[1U] 
        = ((0x38fffU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id
            [1U]) | (((4U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__instruction))
                       ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__id)
                       : ((2U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__instruction))
                           ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__id)
                           : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__id_r))) 
                     << 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[1U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__selected_csr_r;
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[1U][2U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__mulh
           [1U] ? (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__result 
                           >> 0x20U)) : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__result));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__special_case_result 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_greater_than_largest_unsigned_int)
            ? 0xffffffffU : ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_greater_than_largest_signed_int)
                              ? 0x7fffffffU : ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_smaller_than_smallest_signed_int)
                                                ? 0x80000000U
                                                : 0U)));
    if ((0x80U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress_attr))) {
        __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__b 
            = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress_attr) 
                     >> 6U));
        __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__a 
            = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div.remainder;
    } else {
        __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__b 
            = (1U & (IData)((0x20U == (0x30U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress_attr)))));
        __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__a 
            = ((- (IData)((1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress_attr) 
                                 >> 4U)))) | vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div.quotient);
    }
    __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__Vfuncout 
        = (((- (IData)((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__b))) 
            ^ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__a) 
           + (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__b));
    TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET____DOT__rd 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__27__Vfuncout;
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done[1U] 
        = ((0x3dU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
            [1U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__2__KET__.done) 
                     << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done[1U] 
        = ((0x3bU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
            [1U]) | (vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid
                     [1U] << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done[1U] 
        = ((0x37U & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
            [1U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET__.done) 
                     << 3U));
    if ((4U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__instruction))) {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[1U][4U] 
            = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_special) 
                << 4U) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_inexact) 
                          & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_special))));
        vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__.done 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__done;
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[1U][4U] 
            = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_special)
                ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__special_case_result
                : (IData)((0xffffffffULL & (((1ULL 
                                              | ((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_in1)) 
                                                 << 1U)) 
                                             + (((QData)((IData)(
                                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_f2i_int 
                                                                  ^ 
                                                                  (- (IData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_subtract)))))) 
                                                 << 1U) 
                                                | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_subtract)))) 
                                            >> 1U))));
    } else if ((2U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__instruction))) {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[1U][4U] 
            = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__r_invalid_cmp) 
               << 4U);
        vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__.done 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__done;
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[1U][4U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__r_result;
    } else {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[1U][4U] 
            = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_wb.fflags;
        vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__.done 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__done_r;
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[1U][4U] 
            = ((0x200U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U] 
                          << 8U)) | ((0x100U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U] 
                                                << 6U)) 
                                     | ((0x80U & ((
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[2U] 
                                                     >> 4U)) 
                                                   << 7U) 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U] 
                                                     << 4U))) 
                                        | ((0x40U & 
                                            (((~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[2U] 
                                                  >> 4U)) 
                                              << 6U) 
                                             & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U] 
                                                << 2U))) 
                                           | ((0x20U 
                                               & ((((~ 
                                                     (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[2U] 
                                                      >> 4U)) 
                                                    & (~ 
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U] 
                                                        >> 4U))) 
                                                   & (~ 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U])) 
                                                  << 5U)) 
                                              | ((0x10U 
                                                  & (((~ 
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[2U] 
                                                        >> 4U)) 
                                                      & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U]) 
                                                     << 4U)) 
                                                 | (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U] 
                                                      & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[2U] 
                                                         >> 4U)) 
                                                     << 3U) 
                                                    | (((((~ 
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U] 
                                                            >> 4U)) 
                                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[2U] 
                                                             >> 4U)) 
                                                         & (~ 
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U])) 
                                                        << 2U) 
                                                       | ((2U 
                                                           & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[2U] 
                                                               & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U]) 
                                                              >> 3U)) 
                                                          | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[0U] 
                                                              >> 3U) 
                                                             & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr[2U] 
                                                                >> 4U)))))))))));
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
        = ((0xfffU & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U]) 
           | ((IData)((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                        [0U])) << 0x20U) 
                       | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu)))) 
              << 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[1U] 
        = (((IData)((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                      [0U])) << 0x20U) 
                     | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu)))) 
            >> 0x14U) | ((IData)(((((QData)((IData)(
                                                    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                    [0U])) 
                                    << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu))) 
                                  >> 0x20U)) << 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U] 
        = ((0xfffff000U & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U]) 
           | ((IData)(((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                         [0U])) << 0x20U) 
                        | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu))) 
                       >> 0x20U)) >> 0x14U));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
        = ((0xfffffffbU & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U]) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_subtract) 
              << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
        = ((0xfffff0ffU & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U]) 
           | (0xffffff00U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_op_r) 
                              << 0xaU) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_logic_op_r) 
                                          << 8U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array[1U] 
        = ((0xffffffff00000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array
            [1U]) | (IData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellout__genblk4__DOT__genblk1__DOT__axi_bus__data_out)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_valid 
        = (((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bus.data_valid) 
            << 1U) | (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bram.data_valid));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_wb2_float 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_float_table
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__start_algorithm 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo.valid) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__running)));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__selected_csr 
        = (((((((((0x301U == (0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                >> 0x24U)))) 
                  | (0xf11U == (0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                  >> 0x24U))))) 
                 | (0xf12U == (0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                 >> 0x24U))))) 
                | (0xf13U == (0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                >> 0x24U))))) 
               | (0xf14U == (0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                               >> 0x24U))))) 
              | (0x300U == (0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                              >> 0x24U))))) 
             | (0x302U == (0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                             >> 0x24U))))) 
            | (0x303U == (0xfffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                            >> 0x24U)))))
            ? 0U : (((((((((0x304U == (0xfffU & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                         >> 0x24U)))) 
                           | (0x305U == (0xfffU & (IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                           >> 0x24U))))) 
                          | (0x306U == (0xfffU & (IData)(
                                                         (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                          >> 0x24U))))) 
                         | (0x340U == (0xfffU & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                         >> 0x24U))))) 
                        | (0x341U == (0xfffU & (IData)(
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                        >> 0x24U))))) 
                       | (0x342U == (0xfffU & (IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                       >> 0x24U))))) 
                      | (0x343U == (0xfffU & (IData)(
                                                     (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                      >> 0x24U))))) 
                     | (0x344U == (0xfffU & (IData)(
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                     >> 0x24U)))))
                     ? ((0x304U == (0xfffU & (IData)(
                                                     (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                      >> 0x24U))))
                         ? 0U : ((0x305U == (0xfffU 
                                             & (IData)(
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                        >> 0x24U))))
                                  ? 0U : ((0x306U == 
                                           (0xfffU 
                                            & (IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                       >> 0x24U))))
                                           ? 0U : 0U)))
                     : ((((((((((0x3efU <= (0xfffU 
                                            & (IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                       >> 0x24U)))) 
                                & (0x3a0U >= (0xfffU 
                                              & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                         >> 0x24U))))) 
                               | (0xb00U == (0xfffU 
                                             & (IData)(
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                        >> 0x24U))))) 
                              | (0xb02U == (0xfffU 
                                            & (IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                       >> 0x24U))))) 
                             | ((0xb03U <= (0xfffU 
                                            & (IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                       >> 0x24U)))) 
                                & (0xb1fU >= (0xfffU 
                                              & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                         >> 0x24U)))))) 
                            | (0xb80U == (0xfffU & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                            >> 0x24U))))) 
                           | (0xb82U == (0xfffU & (IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                           >> 0x24U))))) 
                          | ((0xb83U <= (0xfffU & (IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                           >> 0x24U)))) 
                             & (0xb9fU >= (0xfffU & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                             >> 0x24U)))))) 
                         | ((0x320U <= (0xfffU & (IData)(
                                                         (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                          >> 0x24U)))) 
                            & (0x33fU >= (0xfffU & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                            >> 0x24U))))))
                         ? (((0x3efU <= (0xfffU & (IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                           >> 0x24U)))) 
                             & (0x3a0U >= (0xfffU & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                             >> 0x24U)))))
                             ? 0U : ((0xb00U == (0xfffU 
                                                 & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                            >> 0x24U))))
                                      ? 0U : ((0xb02U 
                                               == (0xfffU 
                                                   & (IData)(
                                                             (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                              >> 0x24U))))
                                               ? 0U
                                               : ((
                                                   (0xb03U 
                                                    <= 
                                                    (0xfffU 
                                                     & (IData)(
                                                               (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                >> 0x24U)))) 
                                                   & (0xb1fU 
                                                      >= 
                                                      (0xfffU 
                                                       & (IData)(
                                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                  >> 0x24U)))))
                                                   ? 0U
                                                   : 
                                                  ((0xb80U 
                                                    == 
                                                    (0xfffU 
                                                     & (IData)(
                                                               (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                >> 0x24U))))
                                                    ? 0U
                                                    : 
                                                   ((0xb82U 
                                                     == 
                                                     (0xfffU 
                                                      & (IData)(
                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                 >> 0x24U))))
                                                     ? 0U
                                                     : 0U))))))
                         : (((((((((0x100U == (0xfffU 
                                               & (IData)(
                                                         (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                          >> 0x24U)))) 
                                   | (0x102U == (0xfffU 
                                                 & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                            >> 0x24U))))) 
                                  | (0x103U == (0xfffU 
                                                & (IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                           >> 0x24U))))) 
                                 | (0x104U == (0xfffU 
                                               & (IData)(
                                                         (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                          >> 0x24U))))) 
                                | (0x105U == (0xfffU 
                                              & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                         >> 0x24U))))) 
                               | (0x106U == (0xfffU 
                                             & (IData)(
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                        >> 0x24U))))) 
                              | (0x140U == (0xfffU 
                                            & (IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                       >> 0x24U))))) 
                             | (0x141U == (0xfffU & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                             >> 0x24U)))))
                             ? ((0x100U == (0xfffU 
                                            & (IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                       >> 0x24U))))
                                 ? 0U : ((0x102U == 
                                          (0xfffU & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                             >> 0x24U))))
                                          ? 0U : ((0x103U 
                                                   == 
                                                   (0xfffU 
                                                    & (IData)(
                                                              (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                               >> 0x24U))))
                                                   ? 0U
                                                   : 
                                                  ((0x104U 
                                                    == 
                                                    (0xfffU 
                                                     & (IData)(
                                                               (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                >> 0x24U))))
                                                    ? 0U
                                                    : 
                                                   ((0x105U 
                                                     == 
                                                     (0xfffU 
                                                      & (IData)(
                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                 >> 0x24U))))
                                                     ? 0U
                                                     : 
                                                    ((0x106U 
                                                      == 
                                                      (0xfffU 
                                                       & (IData)(
                                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                  >> 0x24U))))
                                                      ? 0U
                                                      : 0U))))))
                             : (((((((((0x142U == (0xfffU 
                                                   & (IData)(
                                                             (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                              >> 0x24U)))) 
                                       | (0x143U == 
                                          (0xfffU & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                             >> 0x24U))))) 
                                      | (0x144U == 
                                         (0xfffU & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                            >> 0x24U))))) 
                                     | (0x180U == (0xfffU 
                                                   & (IData)(
                                                             (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                              >> 0x24U))))) 
                                    | (1U == (0xfffU 
                                              & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                         >> 0x24U))))) 
                                   | (2U == (0xfffU 
                                             & (IData)(
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                        >> 0x24U))))) 
                                  | (3U == (0xfffU 
                                            & (IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                       >> 0x24U))))) 
                                 | (0xc00U == (0xfffU 
                                               & (IData)(
                                                         (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                          >> 0x24U)))))
                                 ? ((0x142U == (0xfffU 
                                                & (IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                           >> 0x24U))))
                                     ? 0U : ((0x143U 
                                              == (0xfffU 
                                                  & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                             >> 0x24U))))
                                              ? 0U : 
                                             ((0x144U 
                                               == (0xfffU 
                                                   & (IData)(
                                                             (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                              >> 0x24U))))
                                               ? 0U
                                               : ((0x180U 
                                                   == 
                                                   (0xfffU 
                                                    & (IData)(
                                                              (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                               >> 0x24U))))
                                                   ? 0U
                                                   : 
                                                  ((1U 
                                                    == 
                                                    (0xfffU 
                                                     & (IData)(
                                                               (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                >> 0x24U))))
                                                    ? 
                                                   (0x1fU 
                                                    & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__fcsr)
                                                    : 
                                                   ((2U 
                                                     == 
                                                     (0xfffU 
                                                      & (IData)(
                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                 >> 0x24U))))
                                                     ? 
                                                    (7U 
                                                     & (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__fcsr 
                                                        >> 5U))
                                                     : 
                                                    ((3U 
                                                      == 
                                                      (0xfffU 
                                                       & (IData)(
                                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                                  >> 0x24U))))
                                                      ? vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__fcsr
                                                      : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle))))))))
                                 : ((0xc01U == (0xfffU 
                                                & (IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                           >> 0x24U))))
                                     ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle)
                                     : ((0xc02U == 
                                         (0xfffU & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                            >> 0x24U))))
                                         ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret)
                                         : (((0xc03U 
                                              <= (0xfffU 
                                                  & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                             >> 0x24U)))) 
                                             & (0xc1fU 
                                                >= 
                                                (0xfffU 
                                                 & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                            >> 0x24U)))))
                                             ? 0U : 
                                            ((0xc80U 
                                              == (0xfffU 
                                                  & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                             >> 0x24U))))
                                              ? (1U 
                                                 & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle 
                                                            >> 0x20U)))
                                              : ((0xc81U 
                                                  == 
                                                  (0xfffU 
                                                   & (IData)(
                                                             (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                              >> 0x24U))))
                                                  ? 
                                                 (1U 
                                                  & (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle 
                                                             >> 0x20U)))
                                                  : 
                                                 ((0xc82U 
                                                   == 
                                                   (0xfffU 
                                                    & (IData)(
                                                              (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r 
                                                               >> 0x24U))))
                                                   ? 
                                                  (1U 
                                                   & (IData)(
                                                             (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret 
                                                              >> 0x20U)))
                                                   : 0U)))))))))));
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__11__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite) 
           & (0x80000000000ULL == (0xff000000000ULL 
                                   & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__10__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite) 
           & (0ULL == (0xff000000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_inc 
        = (1U & (~ ((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__10__Vfuncout) 
                    | (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__11__Vfuncout))));
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__15__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite) 
           & (0x82000000000ULL == (0xff000000000ULL 
                                   & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__14__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite) 
           & (0x2000000000ULL == (0xff000000000ULL 
                                  & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_inc 
        = (3U & ((- (IData)((1U & (~ ((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__14__Vfuncout) 
                                      | (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__15__Vfuncout)))))) 
                 & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__retire) 
                    >> 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[4U] 
        = ((0x1ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[4U]) 
           | (0x1e00U & ((0x1c00U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[6U] 
                                     << 9U)) | (0x200U 
                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[6U] 
                                                   << 5U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_input_next 
        = vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle;
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__8__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite) 
           & (0ULL == (0xff000000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    if (__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__8__Vfuncout) {
        vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_input_next 
            = ((0x100000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_input_next) 
               | (IData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr)));
    }
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__9__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite) 
           & (0x80000000000ULL == (0xff000000000ULL 
                                   & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    if (__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__9__Vfuncout) {
        vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_input_next 
            = ((0xffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_input_next) 
               | ((QData)((IData)((1U & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr))) 
                  << 0x20U));
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_input_next 
        = vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret;
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__12__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite) 
           & (0x2000000000ULL == (0xff000000000ULL 
                                  & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    if (__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__12__Vfuncout) {
        vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_input_next 
            = ((0x100000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_input_next) 
               | (IData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr)));
    }
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__13__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite) 
           & (0x82000000000ULL == (0xff000000000ULL 
                                   & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    if (__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite_en__13__Vfuncout) {
        vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_input_next 
            = ((0xffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_input_next) 
               | ((QData)((IData)((1U & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr))) 
                  << 0x20U));
    }
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__17__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite) 
           & (0x3000000000ULL == (0xff000000000ULL 
                                  & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    __Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__16__Vfuncout 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite) 
           & (0x2000000000ULL == (0xff000000000ULL 
                                  & vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_frm 
        = (7U & ((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__16__Vfuncout)
                  ? vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr
                  : ((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite_en__17__Vfuncout)
                      ? (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr 
                         >> 5U) : (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__fcsr 
                                   >> 5U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__valid_fetch_result 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo.valid) 
           & (4U == (6U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo.data_out))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[0U] 
        = ((0xffffff81U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[0U]) 
           | (0xfffffffeU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_f2i) 
                              << 6U) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fcmp) 
                                         << 5U) | (
                                                   ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_class) 
                                                    << 4U) 
                                                   | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                                      << 1U))))));
    __Vtemp_h041f2230__0[1U] = (((3U & ((IData)((((QData)((IData)(
                                                                  vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                  [0U])) 
                                                  << 0x34U) 
                                                 | (0xfffffffffffffULL 
                                                    & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))) 
                                        >> 0x10U)) 
                                 | ((3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_int_less_than_1) 
                                           >> 0x11U)) 
                                    | ((3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_rs1_expo_unbiased) 
                                              >> 0x1cU)) 
                                       | ((3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_31) 
                                                 >> 0x1dU)) 
                                          | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_30) 
                                             >> 0x1eU))))) 
                                | ((0xfffcU & ((IData)(
                                                       (((QData)((IData)(
                                                                         vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                         [0U])) 
                                                         << 0x34U) 
                                                        | (0xfffffffffffffULL 
                                                           & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))) 
                                               >> 0x10U)) 
                                   | ((IData)(((((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                 [0U])) 
                                                 << 0x34U) 
                                                | (0xfffffffffffffULL 
                                                   & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1)) 
                                               >> 0x20U)) 
                                      << 0x10U)));
    __Vtemp_h041f2230__0[2U] = ((3U & ((IData)(((((QData)((IData)(
                                                                  vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                  [0U])) 
                                                  << 0x34U) 
                                                 | (0xfffffffffffffULL 
                                                    & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1)) 
                                                >> 0x20U)) 
                                       >> 0x10U)) | 
                                (((0xffe0U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased) 
                                              << 5U)) 
                                  | (0xfffcU & ((IData)(
                                                        ((((QData)((IData)(
                                                                           vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                           [0U])) 
                                                           << 0x34U) 
                                                          | (0xfffffffffffffULL 
                                                             & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1)) 
                                                         >> 0x20U)) 
                                                >> 0x10U))) 
                                 | (0xffff0000U & (
                                                   (0x10000U 
                                                    & ((IData)(
                                                               (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                                >> 0x3fU)) 
                                                       << 0x10U)) 
                                                   | (0xffff0000U 
                                                      & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased) 
                                                         << 5U))))));
    __Vtemp_ha7602ea7__0[5U] = (((0xfU & ((((IData)(
                                                    (((QData)((IData)(
                                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                      [0U])) 
                                                      << 0x34U) 
                                                     | (0xfffffffffffffULL 
                                                        & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))) 
                                            >> 8U) 
                                           | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_int_less_than_1) 
                                               >> 9U) 
                                              | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_rs1_expo_unbiased) 
                                                  >> 0x14U) 
                                                 | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_31) 
                                                     >> 0x15U) 
                                                    | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_30) 
                                                       >> 0x16U))))) 
                                          | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed) 
                                              >> 0x17U) 
                                             | (((IData)(
                                                         (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                          >> 0x3fU)) 
                                                 & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed)) 
                                                >> 0x18U)))) 
                                 | ((0xfU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                             >> 0x1bU)) 
                                    | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_swap) 
                                       >> 0x1cU))) 
                                | ((0xf0U & (((0xfffff0U 
                                               & ((IData)(
                                                          (((QData)((IData)(
                                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                            [0U])) 
                                                            << 0x34U) 
                                                           | (0xfffffffffffffULL 
                                                              & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))) 
                                                  >> 8U)) 
                                              | ((0x7ffff0U 
                                                  & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_int_less_than_1) 
                                                     >> 9U)) 
                                                 | ((0xff0U 
                                                     & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_rs1_expo_unbiased) 
                                                        >> 0x14U)) 
                                                    | ((0x7f0U 
                                                        & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_31) 
                                                           >> 0x15U)) 
                                                       | (0x3f0U 
                                                          & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_30) 
                                                             >> 0x16U)))))) 
                                             | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed) 
                                                 >> 0x17U) 
                                                | (((IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                             >> 0x3fU)) 
                                                    & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed)) 
                                                   >> 0x18U)))) 
                                   | (__Vtemp_h041f2230__0[1U] 
                                      << 8U)));
    __Vtemp_hf5cbfb1a__0[4U] = ((0x7fU & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                   >> 0x20U)) 
                                          >> 0x15U)) 
                                | ((0x780U & ((IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                       >> 0x20U)) 
                                              >> 0x15U)) 
                                   | (((((IData)((((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                   [0U])) 
                                                   << 0x34U) 
                                                  | (0xfffffffffffffULL 
                                                     & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))) 
                                         << 0x1fU) 
                                        | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_int_less_than_1) 
                                            << 0x1eU) 
                                           | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_rs1_expo_unbiased) 
                                               << 0x13U) 
                                              | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_31) 
                                                  << 0x12U) 
                                                 | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_30) 
                                                    << 0x11U))))) 
                                       | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed) 
                                           << 0x10U) 
                                          | (((IData)(
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                       >> 0x3fU)) 
                                              & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed)) 
                                             << 0xfU))) 
                                      | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                          << 0xcU) 
                                         | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_swap) 
                                            << 0xbU)))));
    __Vtemp_hf5cbfb1a__0[5U] = ((0x7fU & (((((IData)(
                                                     (((QData)((IData)(
                                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                                       [0U])) 
                                                       << 0x34U) 
                                                      | (0xfffffffffffffULL 
                                                         & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1))) 
                                             >> 1U) 
                                            | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_int_less_than_1) 
                                                >> 2U) 
                                               | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_rs1_expo_unbiased) 
                                                   >> 0xdU) 
                                                  | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_31) 
                                                      >> 0xeU) 
                                                     | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_30) 
                                                        >> 0xfU))))) 
                                           | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed) 
                                               >> 0x10U) 
                                              | (((IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                           >> 0x3fU)) 
                                                  & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed)) 
                                                 >> 0x11U))) 
                                          | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                              >> 0x14U) 
                                             | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_swap) 
                                                >> 0x15U)))) 
                                | (__Vtemp_ha7602ea7__0[5U] 
                                   << 7U));
    __Vtemp_hf5cbfb1a__0[6U] = ((__Vtemp_ha7602ea7__0[5U] 
                                 >> 0x19U) | ((0x780U 
                                               & (__Vtemp_h041f2230__0[1U] 
                                                  >> 0x11U)) 
                                              | ((0x7800U 
                                                  & (__Vtemp_h041f2230__0[1U] 
                                                     >> 0x11U)) 
                                                 | (__Vtemp_h041f2230__0[2U] 
                                                    << 0xfU))));
    __Vtemp_heeb462dd__0[2U] = (((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                          >> 0x20U)) 
                                 >> 0x1fU) | ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2) 
                                                << 0xcU) 
                                               | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                                   [0U] 
                                                   << 0xbU) 
                                                  | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                      [0U] 
                                                      << 0xaU) 
                                                     | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                         [0U] 
                                                         << 9U) 
                                                        | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                           [0U] 
                                                           << 8U))))) 
                                              | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                                  [1U] 
                                                  << 7U) 
                                                 | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                     [1U] 
                                                     << 6U) 
                                                    | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                        [1U] 
                                                        << 5U) 
                                                       | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                           [1U] 
                                                           << 4U) 
                                                          | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                                             << 1U)))))));
    __Vtemp_heeb462dd__0[3U] = (((1U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2) 
                                         >> 0x14U) 
                                        | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                            [0U] >> 0x15U) 
                                           | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                               [0U] 
                                               >> 0x16U) 
                                              | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                  [0U] 
                                                  >> 0x17U) 
                                                 | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                    [0U] 
                                                    >> 0x18U)))))) 
                                 | ((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                           [1U] >> 0x19U)) 
                                    | ((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                              [1U] 
                                              >> 0x1aU)) 
                                       | ((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                 [1U] 
                                                 >> 0x1bU)) 
                                          | ((1U & 
                                              (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                               [1U] 
                                               >> 0x1cU)) 
                                             | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                                >> 0x1fU)))))) 
                                | ((0xfeU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2) 
                                              >> 0x14U) 
                                             | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                                 [0U] 
                                                 >> 0x15U) 
                                                | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                    [0U] 
                                                    >> 0x16U) 
                                                   | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                       [0U] 
                                                       >> 0x17U) 
                                                      | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                         [0U] 
                                                         >> 0x18U)))))) 
                                   | ((0xf00U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2) 
                                                 >> 0x14U)) 
                                      | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                  >> 0x20U)) 
                                         << 0xcU))));
    __Vtemp_heeb462dd__0[4U] = ((1U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                >> 0x20U)) 
                                       >> 0x14U)) | 
                                ((0xfeU & ((IData)(
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                    >> 0x20U)) 
                                           >> 0x14U)) 
                                 | ((0xf00U & ((IData)(
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 
                                                        >> 0x20U)) 
                                               >> 0x14U)) 
                                    | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                       << 0xcU))));
    __Vtemp_heeb462dd__0[5U] = ((1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                       >> 0x14U)) | 
                                ((0xfeU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                           >> 0x14U)) 
                                 | ((0xf00U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                                               >> 0x14U)) 
                                    | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                >> 0x20U)) 
                                       << 0xcU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[0U] 
        = ((0x7fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[0U]) 
           | ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                << 0xcU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                            [0U] << 0xbU)) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                               [0U] 
                                               << 0xaU) 
                                              | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                  [0U] 
                                                  << 9U) 
                                                 | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                     [0U] 
                                                     << 8U) 
                                                    | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                       [0U] 
                                                       << 7U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[1U] 
        = (((0x7fU & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                       >> 0x14U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                    [0U] >> 0x15U))) 
            | ((0x7fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                         [0U] >> 0x16U)) | ((0x7fU 
                                             & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                [0U] 
                                                >> 0x17U)) 
                                            | ((0x7fU 
                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                   [0U] 
                                                   >> 0x18U)) 
                                               | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                  [0U] 
                                                  >> 0x19U))))) 
           | ((0x780U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                          >> 0x14U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                       [0U] >> 0x15U))) 
              | ((0x800U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1) 
                            >> 0x14U)) | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                                   >> 0x20U)) 
                                          << 0xcU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[2U] 
        = ((0x7fU & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                              >> 0x20U)) >> 0x14U)) 
           | ((0x780U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                  >> 0x20U)) >> 0x14U)) 
              | (__Vtemp_heeb462dd__0[2U] << 0xbU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[3U] 
        = ((0x7fU & (__Vtemp_heeb462dd__0[2U] >> 0x15U)) 
           | ((0x780U & (__Vtemp_heeb462dd__0[2U] >> 0x15U)) 
              | (__Vtemp_heeb462dd__0[3U] << 0xbU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[4U] 
        = ((0x7fU & (__Vtemp_heeb462dd__0[3U] >> 0x15U)) 
           | ((0x780U & (__Vtemp_heeb462dd__0[3U] >> 0x15U)) 
              | (__Vtemp_heeb462dd__0[4U] << 0xbU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[5U] 
        = ((0x7fU & (__Vtemp_heeb462dd__0[4U] >> 0x15U)) 
           | ((0x780U & (__Vtemp_heeb462dd__0[4U] >> 0x15U)) 
              | (__Vtemp_heeb462dd__0[5U] << 0xbU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
        = ((0x7fU & (__Vtemp_heeb462dd__0[5U] >> 0x15U)) 
           | ((0x780U & (__Vtemp_heeb462dd__0[5U] >> 0x15U)) 
              | ((0x800U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 
                                     >> 0x20U)) >> 9U)) 
                 | (__Vtemp_hf5cbfb1a__0[4U] << 0xcU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[7U] 
        = ((0x7fU & (__Vtemp_hf5cbfb1a__0[4U] >> 0x14U)) 
           | ((0x780U & (__Vtemp_hf5cbfb1a__0[4U] >> 0x14U)) 
              | ((0x800U & (__Vtemp_hf5cbfb1a__0[4U] 
                            >> 0x14U)) | (__Vtemp_hf5cbfb1a__0[5U] 
                                          << 0xcU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[8U] 
        = ((0x7fU & (__Vtemp_hf5cbfb1a__0[5U] >> 0x14U)) 
           | ((0x780U & (__Vtemp_hf5cbfb1a__0[5U] >> 0x14U)) 
              | ((0x800U & (__Vtemp_hf5cbfb1a__0[5U] 
                            >> 0x14U)) | (__Vtemp_hf5cbfb1a__0[6U] 
                                          << 0xcU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[9U] 
        = (0xfffU & ((0x7fU & (__Vtemp_hf5cbfb1a__0[6U] 
                               >> 0x14U)) | ((0x780U 
                                              & (__Vtemp_hf5cbfb1a__0[6U] 
                                                 >> 0x14U)) 
                                             | (0x800U 
                                                & (__Vtemp_hf5cbfb1a__0[6U] 
                                                   >> 0x14U)))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__4__KET__.ready 
        = (1U & ((~ (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.valid)) 
                 | (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
        = ((0xfc001fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U]) 
           | (0xffffe000U & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_opcode) 
                               << 0x13U) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                            << 0x10U)) 
                             | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fma) 
                                 << 0xfU) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fadd) 
                                              << 0xeU) 
                                             | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fmul) 
                                                << 0xdU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_instruction_id[0U] 
        = ((0x38U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_instruction_id
            [0U]) | (7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_exception_complete)
                            ? (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__exception__BRA__0__KET__.id)
                            : ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out) 
                               >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id[1U] 
        = ((0x3fff8U & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id
            [1U]) | (7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_exception_complete)
                            ? (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__exception__BRA__0__KET__.id)
                            : ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out) 
                               >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U] 
        = ((0xff800000U & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U]) 
           | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_call) 
               << 0x16U) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_return) 
                             << 0x15U) | vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__pc_offset_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U] 
        = ((0x3fffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U]) 
           | ((IData)((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                        [1U])) << 0x20U) 
                       | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu)))) 
              << 0x1eU));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
        = (((IData)((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                      [1U])) << 0x20U) 
                     | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu)))) 
            >> 2U) | ((IData)(((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                 [1U])) 
                                 << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu))) 
                               >> 0x20U)) << 0x1eU));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
        = (((IData)(((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                       [1U])) << 0x20U) 
                      | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu))) 
                     >> 0x20U)) >> 2U) | (((IData)(
                                                   (((QData)((IData)(
                                                                     ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                       [0U] 
                                                                       >> 0x1fU) 
                                                                      & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__br_use_signed)))) 
                                                     << 0x20U) 
                                                    | (QData)((IData)(
                                                                      vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                      [0U])))) 
                                           << 0x1fU) 
                                          | (0x40000000U 
                                             & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                 [1U] 
                                                 >> 1U) 
                                                & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__br_use_signed) 
                                                   << 0x1eU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
        = ((0x3fffffffU & ((IData)((((QData)((IData)(
                                                     ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                       [0U] 
                                                       >> 0x1fU) 
                                                      & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__br_use_signed)))) 
                                     << 0x20U) | (QData)((IData)(
                                                                 vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                 [0U])))) 
                           >> 1U)) | ((0x40000000U 
                                       & ((IData)((
                                                   ((QData)((IData)(
                                                                    ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                      [0U] 
                                                                      >> 0x1fU) 
                                                                     & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__br_use_signed)))) 
                                                    << 0x20U) 
                                                   | (QData)((IData)(
                                                                     vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                     [0U])))) 
                                          >> 1U)) | 
                                      ((IData)(((((QData)((IData)(
                                                                  ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                    [0U] 
                                                                    >> 0x1fU) 
                                                                   & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__br_use_signed)))) 
                                                  << 0x20U) 
                                                 | (QData)((IData)(
                                                                   vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                   [0U]))) 
                                                >> 0x20U)) 
                                       << 0x1fU)));
    vlSelf->instruction_bram_addr = (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc 
                                     >> 2U);
    vlSelf->ddr_axi_arvalid = vlSelf->taiga_sim__DOT__axi_arvalid;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_lr 
        = (IData)((0x88ULL == (0xfcULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__CLZ_delta 
        = (0x1fU & (((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.data_out[0U] 
                      << 0x18U) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.data_out[0U] 
                                   >> 8U)) - ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.data_out[0U] 
                                               << 0x13U) 
                                              | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.data_out[0U] 
                                                 >> 0xdU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__first_cycle_abort 
        = (1U & ((1U & (((0x1fU & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.data_out[0U] 
                                   >> 8U)) - (0x1fU 
                                              & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.data_out[0U] 
                                                 >> 0xdU))) 
                        >> 5U)) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.data_out[0U] 
                                   >> 4U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__cycles_remaining_next 
        = (0xfU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__cycles_remaining) 
                   - (IData)(1U)));
    vlSymsp->TOP__taiga_sim__DOT__mem.wr_data_read 
        = (((IData)(vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_in_progress) 
            & (IData)(vlSelf->ddr_axi_wready)) & (~ (IData)(vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_transfer_complete)));
    vlSelf->taiga_sim__DOT__axi_wvalid = (((IData)(vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_in_progress) 
                                           & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__inflight_count) 
                                              >> 4U)) 
                                          & (~ (IData)(vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_transfer_complete)));
    vlSelf->taiga_sim__DOT__axi_wlast = ((((IData)(vlSelf->taiga_sim__DOT__l2_to_mem__DOT__on_last_burst) 
                                           & (IData)(vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_in_progress)) 
                                          & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__inflight_count) 
                                             >> 4U)) 
                                         & (~ (IData)(vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_transfer_complete)));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[1U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux
            [1U]) | (0x7eU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_previous_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[1U] 
        = ((0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux
            [1U]) | (1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_previous_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[1U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux
            [1U]) | (0x7eU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_previous_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[1U] 
        = ((0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux
            [1U]) | (1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_previous_r)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_mux[3U] 
        = ((IData)(4U) + vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc);
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_addr_fifo.full 
        = (IData)((((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__inflight_count) 
                    >> 4U) & (~ (IData)((0U != (0xfU 
                                                & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__inflight_count)))))));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo.full 
        = (IData)((((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__inflight_count) 
                    >> 4U) & (~ (IData)((0U != (0xfU 
                                                & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__inflight_count)))))));
    __Vfunc_address_range_check__1__addr = vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc;
    __Vfunc_address_range_check__1__Vfuncout = (8U 
                                                == 
                                                (__Vfunc_address_range_check__1__addr 
                                                 >> 0x1cU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__sub_unit_address_match 
        = __Vfunc_address_range_check__1__Vfuncout;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_store 
        = (1U & ((~ (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request 
                             >> 8U))) | ((IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request 
                                                  >> 7U)) 
                                         & (2U != (0x1fU 
                                                   & (IData)(
                                                             (vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request 
                                                              >> 2U)))))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_sc 
        = (IData)((0x8cULL == (0xfcULL & vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo 
        = ((0x800U & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U] 
                      << 0xbU)) | (0x7ffU & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[2U] 
                                             >> 8U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_sign[0U] 
        = (IData)(((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1 
                    ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2) 
                   >> 0x3fU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_inf 
        = (1U & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U] 
                  >> 0xfU) & (~ (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[2U] 
                                 >> 0x13U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__invalid_operation 
        = ((~ (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U] 
               >> 0xcU)) & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[2U] 
                            >> 0x13U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate[0U] 
        = (0x1fffU & ((IData)(0x3ffU) + (((0x7ffU & 
                                           ((IData)(
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1 
                                                     >> 0x34U)) 
                                            + (1U & 
                                               (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_normal))))) 
                                          - (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_left_shift_amt)) 
                                         - ((0x7ffU 
                                             & ((IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2 
                                                         >> 0x34U)) 
                                                + (1U 
                                                   & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_normal))))) 
                                            - (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_left_shift_amt)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_instruction_id[0U] 
        = ((7U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_instruction_id
            [0U]) | (0x38U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[4U] 
                              >> 7U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done[0U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done
            [0U]) | (2U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[4U] 
                           >> 8U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[6U] 
        = ((0x1fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[6U]) 
           | ((IData)((((QData)((IData)((1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U] 
                                                >> 0x1eU) 
                                               ^ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U] 
                                                  >> 0xeU))))) 
                        << 0x3fU) | (0x7fffffffffffffffULL 
                                     & (((QData)((IData)(
                                                         vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])) 
                                         << 0x31U) 
                                        | (((QData)((IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[7U])) 
                                            << 0x11U) 
                                           | ((QData)((IData)(
                                                              vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[6U])) 
                                              >> 0xfU)))))) 
              << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[7U] 
        = (((IData)((((QData)((IData)((1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U] 
                                              >> 0x1eU) 
                                             ^ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U] 
                                                >> 0xeU))))) 
                      << 0x3fU) | (0x7fffffffffffffffULL 
                                   & (((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])) 
                                       << 0x31U) | 
                                      (((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[7U])) 
                                        << 0x11U) | 
                                       ((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[6U])) 
                                        >> 0xfU)))))) 
            >> 0x13U) | ((IData)(((((QData)((IData)(
                                                    (1U 
                                                     & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U] 
                                                         >> 0x1eU) 
                                                        ^ 
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U] 
                                                         >> 0xeU))))) 
                                    << 0x3fU) | (0x7fffffffffffffffULL 
                                                 & (((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])) 
                                                     << 0x31U) 
                                                    | (((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[7U])) 
                                                        << 0x11U) 
                                                       | ((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[6U])) 
                                                          >> 0xfU))))) 
                                  >> 0x20U)) << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[8U] 
        = ((IData)(((((QData)((IData)((1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U] 
                                              >> 0x1eU) 
                                             ^ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U] 
                                                >> 0xeU))))) 
                      << 0x3fU) | (0x7fffffffffffffffULL 
                                   & (((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])) 
                                       << 0x31U) | 
                                      (((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[7U])) 
                                        << 0x11U) | 
                                       ((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[6U])) 
                                        >> 0xfU))))) 
                    >> 0x20U)) >> 0x13U);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U] 
        = ((0xc3ffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U]) 
           | (0x3c000000U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U] 
                             << 9U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U] 
        = ((0xffffefffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U]) 
           | (0x1000U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[6U] 
                         << 4U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U] 
        = ((0xfffffdffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U]) 
           | (0x200U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[6U] 
                        << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U] 
        = ((0xfffff7ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U]) 
           | (0x800U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[6U] 
                        << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U] 
        = ((0x1fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U]) 
           | ((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U])) 
                        << 0x23U) | (((QData)((IData)(
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[1U])) 
                                      << 3U) | ((QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U])) 
                                                >> 0x1dU)))) 
              << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[5U] 
        = (((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U])) 
                      << 0x23U) | (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[1U])) 
                                    << 3U) | ((QData)((IData)(
                                                              vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U])) 
                                              >> 0x1dU)))) 
            >> 0x13U) | ((IData)(((((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U])) 
                                    << 0x23U) | (((QData)((IData)(
                                                                  vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[1U])) 
                                                  << 3U) 
                                                 | ((QData)((IData)(
                                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U])) 
                                                    >> 0x1dU))) 
                                  >> 0x20U)) << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[6U] 
        = ((0xffffe000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[6U]) 
           | ((IData)(((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U])) 
                         << 0x23U) | (((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[1U])) 
                                       << 3U) | ((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U])) 
                                                 >> 0x1dU))) 
                       >> 0x20U)) >> 0x13U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U] 
        = ((0xfc3fffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U]) 
           | (0x3c00000U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U] 
                            << 9U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U] 
        = ((0xfffffbffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U]) 
           | (0x400U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U] 
                        >> 0x12U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U] 
        = ((0x3fffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U]) 
           | (((0x20000000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U])
                ? 5U : 1U) << 0x1eU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U] 
        = ((0xffffff00U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U]) 
           | (0x3fffffffU & ((0xe0U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U] 
                                       >> 0x14U)) | 
                             (((0x20000000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U])
                                ? 5U : 1U) >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[0U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[3U] 
            << 1U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U] 
                      >> 0x1fU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[1U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[4U] 
            << 1U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[3U] 
                      >> 0x1fU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[2U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[5U] 
            << 1U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[4U] 
                      >> 0x1fU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U] 
        = ((0xffc00000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U]) 
           | ((0x200000U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U] 
                            << 0x15U)) | ((((0x20000000U 
                                             & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[2U])
                                             ? 0U : 1U) 
                                           << 0x14U) 
                                          | ((0xfff00U 
                                              & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U] 
                                                 << 7U)) 
                                             | (0xffU 
                                                & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[6U] 
                                                    << 1U) 
                                                   | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[5U] 
                                                      >> 0x1fU)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
        = (((QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
                                   >> 7U)))) << 0x35U) 
           | ((0x1ffffffffffffeULL & (((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[3U])) 
                                       << 0x18U) | 
                                      (0xfffffffffffffeULL 
                                       & ((QData)((IData)(
                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U])) 
                                          >> 8U)))) 
              | (QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
                                       >> 6U))))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.pop 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.valid) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__in_progress)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U] 
        = ((0xff3fffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U]) 
           | (0xffc00000U & ((0x800000U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal
                                            [0U]) << 0x17U)) 
                             | (0x400000U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal
                                              [1U]) 
                                             << 0x16U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U] 
        = ((0xffc001ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U]) 
           | (0xfffffe00U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_fn7) 
                              << 0xfU) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm) 
                                           << 0xcU) 
                                          | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_issue_id) 
                                             << 9U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U] 
        = ((0xffffff00U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U]) 
           | (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                [0U] << 7U) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                [0U] << 6U) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                [0U] 
                                                << 5U) 
                                               | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                  [0U] 
                                                  << 4U)))) 
              | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                  [1U] << 3U) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                  [1U] << 2U) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                  [1U] 
                                                  << 1U) 
                                                 | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                 [1U])))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done[0U] 
        = ((0xeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done
            [0U]) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done
           [1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done[0U] 
        = ((0xdU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done
            [0U]) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done
                     [2U] << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done[0U] 
        = ((7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__intermediate_unit_wb__BRA__3__KET__.done) 
                     << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done[0U] 
        = ((0xbU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done
            [0U]) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                      [0U] ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                      [0U] : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__done_r)) 
                     << 2U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list.data_out 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__lut_ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__read_index];
    vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] = ((0x4ffffU 
                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U]) 
                                                | (0x70000U 
                                                   & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_fetch_hold) 
                                                       << 0x11U) 
                                                      | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_issue_hold) 
                                                         << 0x10U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] = (0x7dfffU 
                                                & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] = ((0x3ffffU 
                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U]) 
                                                | (0x7ffffU 
                                                   & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_init_clear) 
                                                      << 0x12U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] = (0x7e7ffU 
                                                & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc[0U] = (IData)(
                                                       (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc_override)) 
                                                         << 0x20U) 
                                                        | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc))));
    vlSelf->taiga_sim__DOT__cpu__DOT__gc[1U] = ((0xfffffffeU 
                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__gc[1U]) 
                                                | (IData)(
                                                          ((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc_override)) 
                                                             << 0x20U) 
                                                            | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc))) 
                                                           >> 0x20U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__mul_inputs[0U] 
        = (((IData)((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                      [0U])) << 0x20U) 
                     | (QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                       [1U])))) << 2U) 
           | (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                    >> 0xaU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__mul_inputs[1U] 
        = (((IData)((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                      [0U])) << 0x20U) 
                     | (QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                       [1U])))) >> 0x1eU) 
           | ((IData)(((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                         [0U])) << 0x20U) 
                        | (QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                          [1U]))) >> 0x20U)) 
              << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__mul_inputs[2U] 
        = ((IData)(((((QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                      [0U])) << 0x20U) 
                     | (QData)((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                       [1U]))) >> 0x20U)) 
           >> 0x1eU);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_inputs = 
        ((0x3ffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_inputs) 
         | ((QData)((IData)(((0x3ffcU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[4U] 
                                         << 1U)) | 
                             (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                    >> 0xaU))))) << 0x22U));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_inputs = 
        ((0xfffcffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_inputs) 
         | ((QData)((IData)(((2U & ((~ (IData)(((0x400U 
                                                 == 
                                                 (0xc00U 
                                                  & vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U])) 
                                                & (0U 
                                                   == 
                                                   (0x1fU 
                                                    & ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                                        << 4U) 
                                                       | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                          >> 0x1cU))))))) 
                                    << 1U)) | (1U & 
                                               (~ (IData)(
                                                          ((0U 
                                                            == 
                                                            (0x3e000U 
                                                             & vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U])) 
                                                           & (0xc00U 
                                                              == 
                                                              (0xc00U 
                                                               & vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U]))))))))) 
            << 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_inputs = 
        ((0xffff00000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT__csr_inputs) 
         | (IData)((IData)(((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U])
                             ? (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                         >> 0xdU)) : 
                            vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                            [0U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__id[0U] 
        = (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                 >> 0xfU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__id[1U] 
        = (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                 >> 0xfU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__id[2U] 
        = (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                 >> 0xfU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__id[3U] 
        = (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                 >> 0xfU));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot[2U] 
        = vlSelf->taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table
        [(0x3fU & vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U])];
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot[1U] 
        = vlSelf->taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table
        [(vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
          >> 0x1aU)];
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot[0U] 
        = vlSelf->taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table
        [(0x3fU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                   >> 0x14U))];
    taiga_sim__DOT__cpu__DOT__div_inputs[0U] = (((IData)(
                                                         (((QData)((IData)(
                                                                           vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                           [0U])) 
                                                           << 0x20U) 
                                                          | (QData)((IData)(
                                                                            vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                            [1U])))) 
                                                 << 3U) 
                                                | ((6U 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                                       >> 9U)) 
                                                   | ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__genblk6__DOT__prev_div_result_valid) 
                                                        << 0xcU) 
                                                       | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__genblk6__DOT__prev_div_rs_addr)) 
                                                      == 
                                                      (0x1000U 
                                                       | (0xfffU 
                                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                                             >> 1U))))));
    taiga_sim__DOT__cpu__DOT__div_inputs[1U] = (((IData)(
                                                         (((QData)((IData)(
                                                                           vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                           [0U])) 
                                                           << 0x20U) 
                                                          | (QData)((IData)(
                                                                            vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                            [1U])))) 
                                                 >> 0x1dU) 
                                                | ((IData)(
                                                           ((((QData)((IData)(
                                                                              vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                              [0U])) 
                                                              << 0x20U) 
                                                             | (QData)((IData)(
                                                                               vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                               [1U]))) 
                                                            >> 0x20U)) 
                                                   << 3U));
    taiga_sim__DOT__cpu__DOT__div_inputs[2U] = ((IData)(
                                                        ((((QData)((IData)(
                                                                           vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                           [0U])) 
                                                           << 0x20U) 
                                                          | (QData)((IData)(
                                                                            vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                            [1U]))) 
                                                         >> 0x20U)) 
                                                >> 0x1dU);
    vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U] 
        = ((0x3fffU & vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs[2U]) 
           | (0xffffc000U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__ls_offset) 
                              << 0x14U) | ((0xe0000U 
                                            & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                               << 7U)) 
                                           | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_load_r) 
                                               << 0x10U) 
                                              | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_store_r) 
                                                  << 0xfU) 
                                                 | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fence_r) 
                                                    << 0xeU)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[0U] 
        = (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                 >> 0xfU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[0U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[1U] 
        = (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                  [2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U] 
        = (IData)((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                   [2U] >> 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[3U] 
        = (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                  [1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U] 
        = (IData)((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                   [1U] >> 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[5U] 
        = (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                  [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U] 
        = (IData)((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.data
                   [0U] >> 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[8U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[9U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[0xaU] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[0xbU] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__issue[4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[0xcU] 
        = ((0xe000U & (((7U == (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                      >> 0xaU))) ? 
                        (vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__fcsr 
                         >> 5U) : ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                    << 0x16U) | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                                 >> 0xaU))) 
                       << 0xdU)) | vlSelf->taiga_sim__DOT__cpu__DOT__issue[5U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[1U] 
        = (0x3fU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                    >> 0x16U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[1U] 
        = (0x3fU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                    >> 0xeU));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.phys_rs_addr[0U] 
        = (0x3fU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                    >> 1U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.phys_rs_addr[1U] 
        = (0x3fU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                    >> 7U));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__commit_phys_addr[0U] 
        = (0x3fU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                    >> 0x16U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.phys_rs_addr[0U] 
        = (0x3fU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                    >> 0x14U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.phys_rs_addr[1U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
           >> 0x1aU);
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.phys_rs_addr[2U] 
        = (0x3fU & vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id[0U] 
        = ((0x3fff8U & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id
            [0U]) | (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                           >> 0xfU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
        = ((0xfffffffeU & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U]) 
           | (1U & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                       >> 0xcU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
        = ((0xffffff07U & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U]) 
           | (0xf8U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_imm_type)
                         ? ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                             << 0xeU) | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                         >> 0x12U))
                         : vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                        [1U]) << 3U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
        = ((0xfffffffdU & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U]) 
           | (2U & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                     [0U] >> 0x1eU) & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[4U] 
                                       >> 0xaU))));
    taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_imm_type)
            ? VL_EXTENDS_II(32,12, (0xfffU & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[4U] 
                                              >> 1U)))
            : vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
           [1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index_mux[1U] 
        = (0x1fU & ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                     << 4U) | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                               >> 0x1cU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index_mux[1U] 
        = (0x1fU & ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                     << 4U) | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                               >> 0x1cU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U] 
        = ((0xc7ffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U]) 
           | (0x38000000U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                             << 0x11U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U] 
        = ((0xfc7fffffU & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U]) 
           | (0xff800000U & ((0x2000000U & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                            >> 6U)) 
                             | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__jalr) 
                                 << 0x18U) | (0x800000U 
                                              & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                                                 >> 7U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U] 
        = ((0x3ffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U]) 
           | ((IData)((((QData)((IData)(((vlSelf->taiga_sim__DOT__cpu__DOT__issue[5U] 
                                          << 0x13U) 
                                         | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[4U] 
                                            >> 0xdU)))) 
                        << 1U) | (QData)((IData)((1U 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                     >> 0xcU)))))) 
              << 0x1aU));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U] 
        = ((0xf8000000U & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U]) 
           | (((IData)((((QData)((IData)(((vlSelf->taiga_sim__DOT__cpu__DOT__issue[5U] 
                                           << 0x13U) 
                                          | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[4U] 
                                             >> 0xdU)))) 
                         << 1U) | (QData)((IData)((1U 
                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                      >> 0xcU)))))) 
               >> 6U) | ((IData)(((((QData)((IData)(
                                                    ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[5U] 
                                                      << 0x13U) 
                                                     | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[4U] 
                                                        >> 0xdU)))) 
                                    << 1U) | (QData)((IData)(
                                                             (1U 
                                                              & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                                 >> 0xcU))))) 
                                  >> 0x20U)) << 0x1aU)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_issue__BRA__5__KET__.possible_issue 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                  >> 0xcU) & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage) 
                              >> 5U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done[0U] 
        = ((0x3eU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
            [0U]) | (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                            >> 0xcU) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | ((4U >= (7U & (vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [2U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                           [2U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | (((4U >= (7U & (vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                             [2U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [2U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | ((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [0U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_index) 
                 >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                           [0U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | (((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                             [0U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_index) 
                  >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [0U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | ((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [0U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_index) 
                 >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                           [0U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | (((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                             [0U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_index) 
                  >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [0U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | ((4U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [2U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                           [2U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | (((4U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                             [2U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [2U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | ((4U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [2U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                           [2U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | (((4U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                             [2U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [2U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | ((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [0U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_index) 
                 >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                           [0U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
           | (((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                             [0U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_index) 
                  >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__TAPS
                            [0U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | ((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [0U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index) 
                 >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                           [0U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | (((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                             [0U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index) 
                  >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [0U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | ((4U >= (7U & (vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [2U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                           [2U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | (((4U >= (7U & (vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                             [2U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [2U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | ((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [0U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index) 
                 >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                           [0U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | (((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                             [0U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index) 
                  >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [0U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | ((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [0U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index) 
                 >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                           [0U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | (((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                             [0U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index) 
                  >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [0U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
        = vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
           | ((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                            [0U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index) 
                 >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                           [0U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
           | (((2U >= (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                             [0U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index) 
                  >> (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                            [0U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
           | ((5U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                            [3U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                           [3U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
           | (((5U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                             [3U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                            [3U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
           | ((5U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                            [3U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                           [3U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
           | (((5U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                             [3U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__TAPS
                            [3U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback_input)) 
           | ((5U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__TAPS
                            [3U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__TAPS
                           [3U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback_input)) 
           | (((5U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__TAPS
                             [3U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__TAPS
                            [3U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[3U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux
            [3U]) | (0x3eU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index) 
                              << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index_mux[3U] 
        = (0x1fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | ((4U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [2U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                           [2U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | (((4U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                             [2U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [2U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback_input)) 
           | ((5U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__TAPS
                            [3U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__TAPS
                           [3U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback_input)) 
           | (((5U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__TAPS
                             [3U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__TAPS
                            [3U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[3U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux
            [3U]) | (0x3eU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index) 
                              << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index_mux[3U] 
        = (0x1fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | ((4U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [2U][1U] - (IData)(1U)))) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index) 
                 >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                           [2U][1U] - (IData)(1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
           | (((4U >= (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                             [2U][2U] - (IData)(1U)))) 
               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index) 
                  >> (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__TAPS
                            [2U][2U] - (IData)(1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index];
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_data[0U] 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index.value];
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_data[1U] 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__lfsr_read_index.value];
    taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__lfsr_read_index.value];
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests[0U] 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index.value];
    vlSelf->taiga_sim__DOT__l2_arb__DOT__requests[1U] 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index.value];
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__lfsr_read_index.value];
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram
        [vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__lfsr_read_index.value];
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
        = ((0U >= (1U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo.data_out)))
            ? vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__unit_data_array
           [(1U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo.data_out))]
            : 0U);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__new_Q 
        = ((0xfffffffffffffeULL & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt.quotient 
                                   << 1U)) | (QData)((IData)(
                                                             (1U 
                                                              & (~ (IData)(
                                                                           (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__subtraction 
                                                                            >> 0x37U)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__next_subtractend 
        = ((1U & (IData)((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__subtraction 
                          >> 0x37U))) ? ((0xfffffffffffffcULL 
                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__current_subtractend 
                                             << 2U)) 
                                         | (QData)((IData)(
                                                           (3U 
                                                            & (IData)(
                                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__rad 
                                                                       >> 0x36U))))))
            : ((0xfffffffffffffcULL & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__subtraction 
                                       << 2U)) | (QData)((IData)(
                                                                 (3U 
                                                                  & (IData)(
                                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__rad 
                                                                             >> 0x36U)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_1x 
        = (((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x_overflow)
             ? vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div.remainder
             : vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x) 
           - vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__shifted_divisor);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_1x_overflow 
        = (1U & (IData)((1ULL & (((QData)((IData)(((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x_overflow)
                                                    ? vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div.remainder
                                                    : vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x))) 
                                  - (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__shifted_divisor))) 
                                 >> 0x20U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm_left_shift 
        = (0xfffU & ((((((0x800U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                                    >> 1U)) | (0x7ffU 
                                               & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                                                  >> 1U))) 
                        & (- (IData)((1U & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                               >> 0xdU)))))) 
                       - (0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                    >> 0xeU))) & (- (IData)(
                                                            (1U 
                                                             & (~ (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_less_than_left_shift_amt)))))) 
                     + (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                               >> 0xdU) & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                                           >> 1U)))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes[0U] = 0U;
    if ((1U & (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.requests))) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes[0U] = 0U;
    }
    if ((2U & (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.requests))) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes[0U] = 1U;
        vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes[1U] = 1U;
        vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes[1U] = 1U;
    } else {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes[1U] = 1U;
    }
    if ((1U & (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.requests))) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes[1U] = 0U;
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[2U] 
        = ((0xffffffc0U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[2U]) 
           | ((0x3cU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[6U] 
                         << 5U) | (0x1cU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                            >> 0x1bU)))) 
              | ((2U & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                          >> 0x1cU) | (0U != (((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[0U] 
                                                | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[1U]) 
                                               | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[2U]) 
                                              | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[3U]))) 
                        << 1U)) | (1U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[0U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[2U] 
        = ((0x7fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[2U]) 
           | (((IData)((((QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                >> 0x18U)))) 
                         << 0x3fU) | (((QData)((IData)(
                                                       (0x7ffU 
                                                        & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                           >> 0xdU)))) 
                                       << 0x34U) | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm))) 
               << 9U) | ((0x100U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                    >> 4U)) | ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_norm) 
                                               << 7U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[3U] 
        = (((0x7fU & ((IData)((((QData)((IData)((1U 
                                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                    >> 0x18U)))) 
                                << 0x3fU) | (((QData)((IData)(
                                                              (0x7ffU 
                                                               & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                  >> 0xdU)))) 
                                              << 0x34U) 
                                             | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm))) 
                      >> 0x17U)) | ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_norm) 
                                    >> 0x19U)) | ((0x180U 
                                                   & ((IData)(
                                                              (((QData)((IData)(
                                                                                (1U 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                                >> 0x18U)))) 
                                                                << 0x3fU) 
                                                               | (((QData)((IData)(
                                                                                (0x7ffU 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                                >> 0xdU)))) 
                                                                   << 0x34U) 
                                                                  | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm))) 
                                                      >> 0x17U)) 
                                                  | ((IData)(
                                                             ((((QData)((IData)(
                                                                                (1U 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                                >> 0x18U)))) 
                                                                << 0x3fU) 
                                                               | (((QData)((IData)(
                                                                                (0x7ffU 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                                >> 0xdU)))) 
                                                                   << 0x34U) 
                                                                  | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm)) 
                                                              >> 0x20U)) 
                                                     << 9U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[4U] 
        = ((0x1c00U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[4U]) 
           | (0x1fffU & ((0x7fU & ((IData)(((((QData)((IData)(
                                                              (1U 
                                                               & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                  >> 0x18U)))) 
                                              << 0x3fU) 
                                             | (((QData)((IData)(
                                                                 (0x7ffU 
                                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                     >> 0xdU)))) 
                                                 << 0x34U) 
                                                | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm)) 
                                            >> 0x20U)) 
                                   >> 0x17U)) | ((0x200U 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[6U] 
                                                     << 5U)) 
                                                 | (0x180U 
                                                    & ((IData)(
                                                               ((((QData)((IData)(
                                                                                (1U 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                                >> 0x18U)))) 
                                                                  << 0x3fU) 
                                                                 | (((QData)((IData)(
                                                                                (0x7ffU 
                                                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                                                >> 0xdU)))) 
                                                                     << 0x34U) 
                                                                    | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm)) 
                                                                >> 0x20U)) 
                                                       >> 0x17U))))));
    __Vtableidx3 = ((0x80U & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_frac_norm) 
                              << 7U)) | ((((6U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[3U] 
                                                  >> 5U)) 
                                           | (0U != 
                                              (((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[0U] 
                                                 | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[1U]) 
                                                | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[2U]) 
                                               | (0x3fU 
                                                  & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__grs_norm[3U])))) 
                                          << 4U) | 
                                         ((8U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                 >> 0x15U)) 
                                          | (7U & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[5U] 
                                                   >> 0x19U)))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_if_overflow 
        = Vtaiga_sim__ConstPool__TABLE_h95de7929_0[__Vtableidx3];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vcellout__round__roundup 
        = Vtaiga_sim__ConstPool__TABLE_hbdb5e6c2_0[__Vtableidx3];
    vlSelf->retire_ports_pc[0U] = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
        [vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids
        [0U]];
    vlSelf->retire_ports_instruction[0U] = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
        [vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids
        [0U]];
    vlSelf->retire_ports_pc[1U] = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
        [vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids
        [1U]];
    vlSelf->retire_ports_instruction[1U] = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
        [vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__csr_unit_block__retire_ids[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__csr_unit_block__retire_ids[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_ids[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_ids[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_idle 
        = (((~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__inflight_count) 
                >> 3U)) & (~ (IData)((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid))))) 
           & (3U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_ready)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__ready_for_issue_from_lsq 
        = ((3U == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_ready)) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_switch_stall)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_wb2_float 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_wb2_float)) 
           | vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_float_table
           [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__retire_ids_next
           [0U]]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_accu_fcsr 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_accu_fcsr)) 
           | vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__accu_fcsr_table
           [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__retire_ids_next
           [0U]]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_wb2_float 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_wb2_float)) 
           | (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_float_table
              [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__retire_ids_next
              [1U]] << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_accu_fcsr 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_accu_fcsr)) 
           | (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__accu_fcsr_table
              [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__retire_ids_next
              [1U]] << 1U));
    vlSelf->retire_ports_valid[0U] = vlSelf->taiga_sim__DOT__cpu__DOT__retire_port_valid
        [0U];
    vlSelf->retire_ports_valid[1U] = vlSelf->taiga_sim__DOT__cpu__DOT__retire_port_valid
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_port_valid[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__retire_port_valid
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_port_valid[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__retire_port_valid
        [1U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__3__pc 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc;
    __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__3__Vfuncout 
        = (0x1ffffU & (__Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__3__pc 
                       >> 0xbU));
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches)) 
           | ((0x3ffffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry 
                                   >> 5U))) == (0x20000U 
                                                | __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__3__Vfuncout)));
    __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__4__pc 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc;
    __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__4__Vfuncout 
        = (0x1ffffU & (__Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__4__pc 
                       >> 0xbU));
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches)) 
           | (((0x3ffffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry 
                                    >> 0x1cU))) == 
               (0x20000U | __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__4__Vfuncout)) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
        = ((0xfULL & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry) 
           | (0x7fffffffff0ULL & taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
        = ((0x7fffffffff9ULL & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry) 
           | ((QData)((IData)((3U & (IData)((taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr 
                                             >> 1U))))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][6U] 
        = (0xffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
           [0U][6U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][8U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][9U] 
        = ((0xff000000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
            [0U][9U]) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                          [0U] ? ((((6U & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient) 
                                           << 1U)) 
                                    | (0U != (0x7fffffffffffffULL 
                                              & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__PR 
                                                 >> 1U)))) 
                                   & (- (IData)((1U 
                                                 & (~ 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case
                                                    [0U]))))) 
                                  << 5U) : ((0xc0U 
                                             & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__grs
                                                [0U] 
                                                << 5U)) 
                                            | (0x20U 
                                               & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__grs
                                                   [0U] 
                                                   | (0U 
                                                      != vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt.remainder)) 
                                                  << 5U)))) 
                         << 0x10U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden[0U] 
        = ((0xbU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden
            [0U]) | (4U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                            [0U] ? (IData)((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                            >> 0x36U))
                             : (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__result_frac
                                        [0U] >> 0x34U))) 
                           << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_inf 
        = ((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_QNaN)) 
           & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_by_zero) 
              | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_inf)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[5U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[6U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[7U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
        = ((0xffffe000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U]) 
           | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs[8U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
        = ((0x3ffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U]) 
           | (0xfc000000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped
                               [1U] << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped
                                                 [1U] 
                                                 << 0x1eU)) 
                             | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                 [2U] << 0x1dU) | (
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                    [2U] 
                                                    << 0x1cU) 
                                                   | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                                       [2U] 
                                                       << 0x1bU) 
                                                      | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                                         [2U] 
                                                         << 0x1aU)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
        = ((0xfffff000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U]) 
           | (0x3ffffffU & ((((((0x3fff800U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal_swapped
                                               [0U] 
                                               << 0xbU)) 
                                | ((0x3fffc00U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal_swapped
                                                  [1U] 
                                                  << 0xaU)) 
                                   | (0x3fffe00U & 
                                      (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal
                                       [2U] << 9U)))) 
                               | ((0x3ffff00U & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_hidden_bit_pre_normalized_swapped) 
                                                 << 8U)) 
                                  | ((0x3ffff80U & 
                                      ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_hidden_bit_pre_normalized_swapped) 
                                       << 7U)) | (0x3ffffc0U 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit
                                                     [2U] 
                                                     << 6U))))) 
                              | ((0x3ffffe0U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf_swapped
                                                [0U] 
                                                << 5U)) 
                                 | ((0x3fffff0U & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN_swapped
                                                   [0U] 
                                                   << 4U)) 
                                    | ((0x3fffff8U 
                                        & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped
                                           [0U] << 3U)) 
                                       | (0x3fffffcU 
                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped
                                             [0U] << 2U)))))) 
                             | ((0x3fffffeU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf_swapped
                                               [1U] 
                                               << 1U)) 
                                | (0x3ffffffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN_swapped
                                                 [1U] 
                                                 | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped
                                                     [1U] 
                                                     >> 1U) 
                                                    | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped
                                                       [1U] 
                                                       >> 2U)))))) 
                            | ((0x3ffffffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf
                                              [2U] 
                                              >> 3U)) 
                               | ((0x3ffffffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                                 [2U] 
                                                 >> 4U)) 
                                  | ((0x3ffffffU & 
                                      (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                       [2U] >> 5U)) 
                                     | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero
                                        [2U] >> 6U)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U] 
        = ((0xffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U]) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_pre_normalize_shift_amt) 
              << 0x18U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[1U] 
        = (((0xff0000U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized) 
                          << 0x10U)) | ((0xff8000U 
                                         & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_hidden_bit_pre_normalized) 
                                            << 0xfU)) 
                                        | ((0xffc000U 
                                            & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_hidden_bit_pre_normalized) 
                                               << 0xeU)) 
                                           | ((0xfffff8U 
                                               & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_pre_normalize_shift_amt) 
                                                  << 3U)) 
                                              | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_pre_normalize_shift_amt) 
                                                 >> 8U))))) 
           | (0xff000000U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized) 
                             << 0x10U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[2U] 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized) 
             >> 0x10U) | (0xff0000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized 
                                                >> 0x20U)) 
                                       << 0x10U))) 
           | (0xff000000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized 
                                      >> 0x20U)) << 0x10U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[3U] 
        = ((((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized 
                      >> 0x20U)) >> 0x10U) | (0xff0000U 
                                              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized) 
                                                 << 0x10U))) 
           | (0xff000000U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized) 
                             << 0x10U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[4U] 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized) 
             >> 0x10U) | (0xff0000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized 
                                                >> 0x20U)) 
                                       << 0x10U))) 
           | (0xff000000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized 
                                      >> 0x20U)) << 0x10U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U] 
        = ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized 
                    >> 0x20U)) >> 0x10U);
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap 
        = (1U & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                   [1U] | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                           [1U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                           [0U])) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                  [0U]) | (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                             [1U] | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                                     [1U] & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                     [0U])) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN
                            [0U]) | (((~ (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped 
                                                  >> 0x3fU))) 
                                      & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))) 
                                     | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped 
                                                 >> 0x3fU)) 
                                        & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
        = ((0x7fffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U]) 
           | ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt_swapped) 
              << 0x17U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xaU] 
        = (((0x7fe000U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs3) 
                          << 0xdU)) | ((0x7ffffcU & 
                                        ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt_swapped) 
                                         << 2U)) | 
                                       ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt_swapped) 
                                        >> 9U))) | 
           (0xff800000U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs3) 
                           << 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xbU] 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs3) 
             >> 0x13U) | (0x7fe000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs3 
                                                >> 0x20U)) 
                                       << 0xdU))) | 
           (0xff800000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs3 
                                    >> 0x20U)) << 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xcU] 
        = ((((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs3 
                      >> 0x20U)) >> 0x13U) | (0x7fe000U 
                                              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped) 
                                                 << 0xdU))) 
           | (0xff800000U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped) 
                             << 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xdU] 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped) 
             >> 0x13U) | (0x7fe000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped 
                                                >> 0x20U)) 
                                       << 0xdU))) | 
           (0xff800000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped 
                                    >> 0x20U)) << 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU] 
        = ((((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped 
                      >> 0x20U)) >> 0x13U) | (0x7fe000U 
                                              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped) 
                                                 << 0xdU))) 
           | (0xff800000U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped) 
                             << 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xfU] 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped) 
             >> 0x13U) | (0x7fe000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped 
                                                >> 0x20U)) 
                                       << 0xdU))) | 
           (0xff800000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped 
                                    >> 0x20U)) << 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0x10U] 
        = ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped 
                    >> 0x20U)) >> 0x13U);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[0U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list.data_out) 
                     << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe[0U] 
        = ((0xdU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe
            [0U]) | (2U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                    [1U] >> 0x35U)) 
                           << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden[0U] 
        = ((0xdU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden
            [0U]) | (2U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                    [1U] >> 0x34U)) 
                           << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[1U][3U] 
        = TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__4__KET____DOT__rd;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_rd[0U][0U] 
        = (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array
                            [(1U & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out) 
                                    >> 1U))])) << 0x20U) 
           | (QData)((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array
                              [(1U & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out) 
                                      >> 1U))] >> 0x20U))));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_muxed_load_data 
        = ((1U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out))
            ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array
                      [(1U & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out) 
                              >> 1U))]) : (IData)((
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array
                                                   [
                                                   (1U 
                                                    & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out) 
                                                       >> 1U))] 
                                                   >> 0x20U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done[1U] 
        = ((0x2fU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
            [1U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__.done) 
                     << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done[0U] 
        = ((2U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done
            [0U]) | (((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_valid)) 
                      | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_exception_complete)) 
                     & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out) 
                        >> 5U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done[1U] 
        = ((0x3eU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
            [1U]) | (((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_valid)) 
                      | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_exception_complete)) 
                     & (~ ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out) 
                           >> 5U))));
    __Vtemp_hf3c0533d__0[1U] = ((0x1ffU & ((IData)(
                                                   (((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
                                                                     [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])) 
                                                     << 0x20U) 
                                                    | (QData)((IData)(
                                                                      vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
                                                                      [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])))) 
                                           >> 0x16U)) 
                                | ((0x200U & ((IData)(
                                                      (((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
                                                                        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])) 
                                                        << 0x20U) 
                                                       | (QData)((IData)(
                                                                         vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
                                                                         [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])))) 
                                              >> 0x16U)) 
                                   | ((IData)(((((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
                                                                 [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])) 
                                                 << 0x20U) 
                                                | (QData)((IData)(
                                                                  vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
                                                                  [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id]))) 
                                               >> 0x20U)) 
                                      << 0xaU)));
    __Vtemp_hf3c0533d__0[2U] = ((0x1ffU & ((IData)(
                                                   ((((QData)((IData)(
                                                                      vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
                                                                      [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])) 
                                                      << 0x20U) 
                                                     | (QData)((IData)(
                                                                       vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
                                                                       [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id]))) 
                                                    >> 0x20U)) 
                                           >> 0x16U)) 
                                | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id) 
                                    << 0xaU) | (0x200U 
                                                & ((IData)(
                                                           ((((QData)((IData)(
                                                                              vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
                                                                              [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])) 
                                                              << 0x20U) 
                                                             | (QData)((IData)(
                                                                               vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
                                                                               [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id]))) 
                                                            >> 0x20U)) 
                                                   >> 0x16U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] = 
        (((((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
                                      [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])) 
                      << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
                                                  [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])))) 
            << 0xcU) | (0x800U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__fetched_count_neg) 
                                  << 8U))) | ((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__fetch_metadata_table
                                               [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id] 
                                               << 5U) 
                                              | ((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__is_float_table
                                                  [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id] 
                                                  << 4U) 
                                                 | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_wb2_float) 
                                                     << 3U) 
                                                    | (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__accu_fcsr_table
                                                       [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id] 
                                                       << 2U))))) 
         | ((vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__need_int_data_table
             [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id] 
             << 1U) | vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_int_table
            [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id]));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] = 
        (((3U & ((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table
                                           [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])) 
                           << 0x20U) | (QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table
                                                       [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id])))) 
                 >> 0x14U)) | ((3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__fetch_metadata_table
                                      [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id] 
                                      >> 0x1bU)) | 
                               ((3U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__is_float_table
                                       [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id] 
                                       >> 0x1cU)) | 
                                ((3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_wb2_float) 
                                        >> 0x1dU)) 
                                 | (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__accu_fcsr_table
                                    [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id] 
                                    >> 0x1eU))))) | 
         (__Vtemp_hf3c0533d__0[1U] << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode[2U] = 
        ((__Vtemp_hf3c0533d__0[1U] >> 0x1eU) | (__Vtemp_hf3c0533d__0[2U] 
                                                << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_complete 
        = (((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo.valid) 
            & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__valid_fetch_result))) 
           | (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram.data_valid));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__unordered 
        = (IData)((0U != (0x330000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[2U])));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__class_issue.new_request 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__3__KET__.new_request) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[0U] 
              >> 4U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__f2i_issue.new_request 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__3__KET__.new_request) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[0U] 
              >> 6U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__cmp_issue.new_request 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__3__KET__.new_request) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[0U] 
              >> 5U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__sign_equ 
        = (1U & (~ ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                     ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[4U]) 
                    >> 0x16U)));
    VL_EXTEND_WQ(84,53, __Vtemp_h94d9bf51__0, (0x1fffffffffffffULL 
                                               & (((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[8U])) 
                                                   << 0x15U) 
                                                  | ((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[7U])) 
                                                     >> 0xbU))));
    VL_SHIFTL_WWI(84,84,11, __Vtemp_hf7c80da1__0, __Vtemp_h94d9bf51__0, 
                  (0x7ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[9U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac[0U] 
        = __Vtemp_hf7c80da1__0[0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac[1U] 
        = __Vtemp_hf7c80da1__0[1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac[2U] 
        = (0xfffffU & __Vtemp_hf7c80da1__0[2U]);
    vlSelf->ddr_axi_wvalid = vlSelf->taiga_sim__DOT__axi_wvalid;
    vlSelf->ddr_axi_wlast = vlSelf->taiga_sim__DOT__axi_wlast;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__advance = 
        ((0U != (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.requests)) 
         & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_addr_fifo.full)));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__0__KET__.push 
        = (((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_valid) 
            & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_store)) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_id_v)));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__inv_response_fifos__BRA__1__KET__.push 
        = (((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_valid) 
            & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_store)) 
           & (~ ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_id_v) 
                 >> 1U)));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match)) 
           | (vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation_address
              [0U] == (0x3fffffffU & (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request 
                                              >> 0xdU)))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__revoke_reservation 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__revoke_reservation)) 
           | ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_sc) 
              | ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_store) 
                 & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match)) 
           | ((vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation_address
               [1U] == (0x3fffffffU & (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request 
                                               >> 0xdU)))) 
              << 1U));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__revoke_reservation 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__revoke_reservation)) 
           | (((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_sc) 
               << 1U) | (0xfffffffeU & (((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_store) 
                                         << 1U) & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match)))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt.radicand 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo))
            ? (0x10000000000000ULL | (0xfffffffffffffULL 
                                      & (((QData)((IData)(
                                                          vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[2U])) 
                                          << 0x2cU) 
                                         | (((QData)((IData)(
                                                             vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[1U])) 
                                             << 0xcU) 
                                            | ((QData)((IData)(
                                                               vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U])) 
                                               >> 0x14U)))))
            : (0x8000000000000ULL | (0x7ffffffffffffULL 
                                     & (((QData)((IData)(
                                                         vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[2U])) 
                                         << 0x2bU) 
                                        | (((QData)((IData)(
                                                            vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[1U])) 
                                            << 0xbU) 
                                           | ((QData)((IData)(
                                                              vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U])) 
                                              >> 0x15U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_QNaN 
        = (IData)(((0U != (0x6000U & vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U])) 
                   | (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__invalid_operation)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__right_shift 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate
                  [1U] >> 0xcU) | (~ (IData)((0U != 
                                              (0xfffU 
                                               & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate
                                               [1U]))))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[0U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[0U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[0U]
               : ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[1U] 
                   << 0x1dU) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[0U] 
                                >> 3U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[1U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[1U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[1U]
               : ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[2U] 
                   << 0x1dU) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[1U] 
                                >> 3U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[2U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[2U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[2U]
               : ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[3U] 
                   << 0x1dU) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[2U] 
                                >> 3U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[3U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[3U]
               : ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[4U] 
                   << 0x1dU) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[3U] 
                                >> 3U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[4U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[4U]
               : ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[5U] 
                   << 0x1dU) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[4U] 
                                >> 3U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[5U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[5U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[5U]
               : ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[6U] 
                   << 0x1dU) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[5U] 
                                >> 3U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[6U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[6U]
               : ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[7U] 
                   << 0x1dU) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[6U] 
                                >> 3U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[7U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[7U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[7U]
               : ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[8U] 
                   << 0x1dU) | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[7U] 
                                >> 3U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[8U] 
        = (Vtaiga_sim__ConstPool__CONST_h5285fb67_0[8U] 
           & ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U])
               ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs[8U]
               : (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.data_out[8U] 
                  >> 3U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs 
        = ((0x1fcU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs)) 
           | (((IData)((0x3fU == (0x3fU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
                                                   >> 6U))))) 
               << 1U) | (0x3fU == (0x3fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs 
        = ((0x1f3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs)) 
           | ((((IData)((0x3fU == (0x3fU & (IData)(
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
                                                    >> 0x12U))))) 
                << 1U) | (0x3fU == (0x3fU & (IData)(
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
                                                     >> 0xcU))))) 
              << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs 
        = ((0x1cfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs)) 
           | ((((IData)((0x3fU == (0x3fU & (IData)(
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
                                                    >> 0x1eU))))) 
                << 1U) | (0x3fU == (0x3fU & (IData)(
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
                                                     >> 0x18U))))) 
              << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs 
        = ((0x13fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs)) 
           | ((((IData)((0x3fU == (0x3fU & (IData)(
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
                                                    >> 0x2aU))))) 
                << 1U) | (0x3fU == (0x3fU & (IData)(
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
                                                     >> 0x24U))))) 
              << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs 
        = ((0xffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs)) 
           | ((IData)((0x3fU == (0x3fU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup 
                                                  >> 0x30U))))) 
              << 8U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready[1U] 
        = (1U & (((~ (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo.valid)) 
                  | (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__input_fifo.pop)) 
                 & ((~ (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.valid)) 
                    | (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.pop))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel[0U] 
        = (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom 
                 >> (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done
                              [0U] << 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[0U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux
            [0U]) | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list.data_out) 
                     << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[0U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list.data_out;
    __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__b 
        = ((~ (taiga_sim__DOT__cpu__DOT__div_inputs[0U] 
               >> 1U)) & (taiga_sim__DOT__cpu__DOT__div_inputs[2U] 
                          >> 2U));
    __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__a 
        = ((taiga_sim__DOT__cpu__DOT__div_inputs[2U] 
            << 0x1dU) | (taiga_sim__DOT__cpu__DOT__div_inputs[1U] 
                         >> 3U));
    __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__Vfuncout 
        = (((- (IData)((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__b))) 
            ^ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__a) 
           + (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__b));
    taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__25__Vfuncout;
    __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__b 
        = (1U & ((~ (taiga_sim__DOT__cpu__DOT__div_inputs[0U] 
                     >> 1U)) & (taiga_sim__DOT__cpu__DOT__div_inputs[1U] 
                                >> 2U)));
    __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__a 
        = ((taiga_sim__DOT__cpu__DOT__div_inputs[1U] 
            << 0x1dU) | (taiga_sim__DOT__cpu__DOT__div_inputs[0U] 
                         >> 3U));
    __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__Vfuncout 
        = (((- (IData)((IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__b))) 
            ^ __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__a) 
           + (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__b));
    taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__negate_if__26__Vfuncout;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero[0U] 
        = (IData)(((0U == (0xc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U])) 
                   & ((~ (IData)((0U != (0x7ffU & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U] 
                                                   >> 0x14U))))) 
                      & (~ (IData)((0U != (0x3ffffffffffffULL 
                                           & (((QData)((IData)(
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U])) 
                                               << 0x20U) 
                                              | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[5U]))))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN[0U] 
        = ((IData)((0x7ff80000U == (0x7ffc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U]))) 
           & (~ (IData)((0U != (0x3ffffffffffffULL 
                                & (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U])) 
                                    << 0x20U) | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[5U]))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN[0U] 
        = ((IData)((0x7ff40000U == (0x7ffc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U]))) 
           & (~ (IData)((0U != (0x3ffffffffffffULL 
                                & (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U])) 
                                    << 0x20U) | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[5U]))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf[0U] 
        = (IData)(((0x7ff00000U == (0x7ff00000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U])) 
                   & (~ (IData)((0U != (0xfffffffffffffULL 
                                        & (((QData)((IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U])) 
                                            << 0x20U) 
                                           | (QData)((IData)(
                                                             vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[5U])))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero[1U] 
        = (IData)(((0U == (0xc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U])) 
                   & ((~ (IData)((0U != (0x7ffU & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U] 
                                                   >> 0x14U))))) 
                      & (~ (IData)((0U != (0x3ffffffffffffULL 
                                           & (((QData)((IData)(
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U])) 
                                               << 0x20U) 
                                              | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[3U]))))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN[1U] 
        = ((IData)((0x7ff80000U == (0x7ffc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U]))) 
           & (~ (IData)((0U != (0x3ffffffffffffULL 
                                & (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U])) 
                                    << 0x20U) | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[3U]))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN[1U] 
        = ((IData)((0x7ff40000U == (0x7ffc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U]))) 
           & (~ (IData)((0U != (0x3ffffffffffffULL 
                                & (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U])) 
                                    << 0x20U) | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[3U]))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf[1U] 
        = (IData)(((0x7ff00000U == (0x7ff00000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U])) 
                   & (~ (IData)((0U != (0xfffffffffffffULL 
                                        & (((QData)((IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U])) 
                                            << 0x20U) 
                                           | (QData)((IData)(
                                                             vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[3U])))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero[2U] 
        = (IData)(((0U == (0xc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U])) 
                   & ((~ (IData)((0U != (0x7ffU & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U] 
                                                   >> 0x14U))))) 
                      & (~ (IData)((0U != (0x3ffffffffffffULL 
                                           & (((QData)((IData)(
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U])) 
                                               << 0x20U) 
                                              | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[1U]))))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN[2U] 
        = ((IData)((0x7ff80000U == (0x7ffc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U]))) 
           & (~ (IData)((0U != (0x3ffffffffffffULL 
                                & (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U])) 
                                    << 0x20U) | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[1U]))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN[2U] 
        = ((IData)((0x7ff40000U == (0x7ffc0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U]))) 
           & (~ (IData)((0U != (0x3ffffffffffffULL 
                                & (((QData)((IData)(
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U])) 
                                    << 0x20U) | (QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[1U]))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf[2U] 
        = (IData)(((0x7ff00000U == (0x7ff00000U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U])) 
                   & (~ (IData)((0U != (0xfffffffffffffULL 
                                        & (((QData)((IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U])) 
                                            << 0x20U) 
                                           | (QData)((IData)(
                                                             vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[1U])))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_fmul 
        = (IData)((0x45U == (0x47U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[0xaU])));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_fadd 
        = (IData)((5U == (0x47U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[0xaU])));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit[0U] 
        = (0U != (0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U] 
                            >> 0x14U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit[1U] 
        = (0U != (0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U] 
                            >> 0x14U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit[2U] 
        = (0U != (0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[2U] 
                            >> 0x14U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[2U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[3U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[3U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[4U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[5U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_rf_issue.phys_rs_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U] 
        = ((0xfffU & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U]) 
           | ((IData)((((QData)((IData)(((taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data 
                                          >> 0x1fU) 
                                         & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                               >> 0xaU))))) 
                        << 0x20U) | (QData)((IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data)))) 
              << 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U] 
        = (((IData)((((QData)((IData)(((taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data 
                                        >> 0x1fU) & 
                                       (~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                           >> 0xaU))))) 
                      << 0x20U) | (QData)((IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data)))) 
            >> 0x14U) | (((IData)((((QData)((IData)(
                                                    (1U 
                                                     & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                         [0U] 
                                                         >> 0x1fU) 
                                                        & (~ 
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                                            >> 0xaU)))))) 
                                    << 0x20U) | (QData)((IData)(
                                                                vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                [0U])))) 
                          << 0xdU) | ((IData)(((((QData)((IData)(
                                                                 ((taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data 
                                                                   >> 0x1fU) 
                                                                  & (~ 
                                                                     (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                                                      >> 0xaU))))) 
                                                 << 0x20U) 
                                                | (QData)((IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data))) 
                                               >> 0x20U)) 
                                      << 0xcU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U] 
        = (0x3fffU & (((0xfffU & ((IData)((((QData)((IData)(
                                                            (1U 
                                                             & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                 [0U] 
                                                                 >> 0x1fU) 
                                                                & (~ 
                                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                                                    >> 0xaU)))))) 
                                            << 0x20U) 
                                           | (QData)((IData)(
                                                             vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                             [0U])))) 
                                  >> 0x13U)) | ((IData)(
                                                        ((((QData)((IData)(
                                                                           ((taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data 
                                                                             >> 0x1fU) 
                                                                            & (~ 
                                                                               (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                                                                >> 0xaU))))) 
                                                           << 0x20U) 
                                                          | (QData)((IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_rs2_data))) 
                                                         >> 0x20U)) 
                                                >> 0x14U)) 
                      | ((0x1000U & ((IData)((((QData)((IData)(
                                                               (1U 
                                                                & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                    [0U] 
                                                                    >> 0x1fU) 
                                                                   & (~ 
                                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                                                       >> 0xaU)))))) 
                                               << 0x20U) 
                                              | (QData)((IData)(
                                                                vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                [0U])))) 
                                     >> 0x13U)) | ((IData)(
                                                           ((((QData)((IData)(
                                                                              (1U 
                                                                               & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                                [0U] 
                                                                                >> 0x1fU) 
                                                                                & (~ 
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__issue[3U] 
                                                                                >> 0xaU)))))) 
                                                              << 0x20U) 
                                                             | (QData)((IData)(
                                                                               vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__rf_issue.data
                                                                               [0U]))) 
                                                            >> 0x20U)) 
                                                   << 0xdU))));
    taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__carry_in 
        = (1U & ((0x20000000U & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U])
                  ? ((((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                        >> 0x1fU) | (~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
                                        >> 0x1eU))) 
                      & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                         | (~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
                               >> 0x1fU)))) | (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                               & (~ 
                                                  (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
                                                   >> 0x1fU))))
                  : ((((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                        >> 0x1fU) & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
                                     >> 0x1eU)) | (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0x1fU)) 
                                                   & (~ 
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
                                                       >> 0x1eU)))) 
                     & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                         & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
                            >> 0x1fU)) | ((~ vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U]) 
                                          & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
                                                >> 0x1fU)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0x7fffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x8000U & ((0x8000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                      >> 0x10U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0x1eU)) 
                                                   << 0xfU))) 
                         | ((0x8000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0x10U)) 
                            | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                   >> 0x1eU)) << 0xfU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xbfffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x4000U & (((0x1c000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xfU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x1cU)) 
                                         << 0xeU)) 
                                       & ((0xc000U 
                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                              >> 0x10U)) 
                                          | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                 >> 0x1dU)) 
                                             << 0xeU)))) 
                          | (0xc000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0x10U) 
                                        & ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                               >> 0x1dU)) 
                                           << 0xeU)))) 
                         | (((0x1c000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xfU)) 
                             | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                    >> 0x1cU)) << 0xeU)) 
                            & ((0xc000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                           >> 0x10U)) 
                               | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                      >> 0x1dU)) << 0xeU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xdfffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x2000U & (((0x3e000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xeU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x1aU)) 
                                         << 0xdU)) 
                                       & ((0x1e000U 
                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                              >> 0xfU)) 
                                          | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                 >> 0x1bU)) 
                                             << 0xdU)))) 
                          | (0x1e000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xfU) 
                                         & ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 0x1bU)) 
                                            << 0xdU)))) 
                         | (((0x3e000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xeU)) 
                             | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                    >> 0x1aU)) << 0xdU)) 
                            & ((0x1e000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 0xfU)) 
                               | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                      >> 0x1bU)) << 0xdU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xefffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x1000U & (((0x7f000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xdU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x18U)) 
                                         << 0xcU)) 
                                       & ((0x3f000U 
                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                              >> 0xeU)) 
                                          | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                 >> 0x19U)) 
                                             << 0xcU)))) 
                          | (0x3f000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xeU) 
                                         & ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 0x19U)) 
                                            << 0xcU)))) 
                         | (((0x7f000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xdU)) 
                             | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                    >> 0x18U)) << 0xcU)) 
                            & ((0x3f000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 0xeU)) 
                               | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                      >> 0x19U)) << 0xcU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xf7ffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x800U & (((0xff800U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0xcU) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x16U)) 
                                        << 0xbU)) & 
                                      ((0x7f800U & 
                                        (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xdU)) 
                                       | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 0x17U)) 
                                          << 0xbU)))) 
                         | (0x7f800U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xdU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x17U)) 
                                         << 0xbU)))) 
                        | (((0xff800U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xcU)) 
                            | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                   >> 0x16U)) << 0xbU)) 
                           & ((0x7f800U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                           >> 0xdU)) 
                              | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                     >> 0x17U)) << 0xbU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xfbffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x400U & (((0x1ffc00U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xbU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x14U)) 
                                         << 0xaU)) 
                                       & ((0xffc00U 
                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                              >> 0xcU)) 
                                          | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                 >> 0x15U)) 
                                             << 0xaU)))) 
                         | (0xffc00U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xcU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x15U)) 
                                         << 0xaU)))) 
                        | (((0x1ffc00U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xbU)) 
                            | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                   >> 0x14U)) << 0xaU)) 
                           & ((0xffc00U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                           >> 0xcU)) 
                              | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                     >> 0x15U)) << 0xaU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xfdffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x200U & (((0x3ffe00U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xaU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x12U)) 
                                         << 9U)) & 
                                       ((0x1ffe00U 
                                         & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 0xbU)) 
                                        | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                               >> 0x13U)) 
                                           << 9U)))) 
                         | (0x1ffe00U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xbU) 
                                         & ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 0x13U)) 
                                            << 9U)))) 
                        | (((0x3ffe00U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xaU)) 
                            | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                   >> 0x12U)) << 9U)) 
                           & ((0x1ffe00U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 0xbU)) 
                              | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                     >> 0x13U)) << 9U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xfeffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x100U & (((0x7fff00U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 9U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0x10U)) 
                                                   << 8U)) 
                                       & ((0x3fff00U 
                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                              >> 0xaU)) 
                                          | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                 >> 0x11U)) 
                                             << 8U)))) 
                         | (0x3fff00U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xaU) 
                                         & ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 0x11U)) 
                                            << 8U)))) 
                        | (((0x7fff00U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 9U)) | 
                            ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                 >> 0x10U)) << 8U)) 
                           & ((0x3fff00U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 0xaU)) 
                              | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                     >> 0x11U)) << 8U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xff7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x80U & (((0xffff80U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 8U) & ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 0xeU)) 
                                                  << 7U)) 
                                      & ((0x7fff80U 
                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                             >> 9U)) 
                                         | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 0xfU)) 
                                            << 7U)))) 
                        | (0x7fff80U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 9U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0xfU)) 
                                                   << 7U)))) 
                       | (((0xffff80U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 8U)) | 
                           ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                >> 0xeU)) << 7U)) & 
                          ((0x7fff80U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 9U)) | 
                           ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                >> 0xfU)) << 7U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xffbfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x40U & (((0x1ffffc0U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 7U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0xcU)) 
                                                   << 6U)) 
                                       & ((0xffffc0U 
                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                              >> 8U)) 
                                          | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                 >> 0xdU)) 
                                             << 6U)))) 
                        | (0xffffc0U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 8U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0xdU)) 
                                                   << 6U)))) 
                       | (((0x1ffffc0U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 7U)) | 
                           ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                >> 0xcU)) << 6U)) & 
                          ((0xffffc0U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 8U)) | 
                           ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                >> 0xdU)) << 6U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xffdfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x20U & (((0x3ffffe0U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 6U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0xaU)) 
                                                   << 5U)) 
                                       & ((0x1ffffe0U 
                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                              >> 7U)) 
                                          | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                 >> 0xbU)) 
                                             << 5U)))) 
                        | (0x1ffffe0U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 7U) & 
                                         ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 0xbU)) 
                                          << 5U)))) 
                       | (((0x3ffffe0U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 6U)) | 
                           ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                >> 0xaU)) << 5U)) & 
                          ((0x1ffffe0U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 7U)) | 
                           ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                >> 0xbU)) << 5U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xffefU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (0x10U & (((0x7fffff0U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 5U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 8U)) 
                                                   << 4U)) 
                                       & ((0x3fffff0U 
                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                              >> 6U)) 
                                          | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                 >> 9U)) 
                                             << 4U)))) 
                        | (0x3fffff0U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 6U) & 
                                         ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 9U)) 
                                          << 4U)))) 
                       | (((0x7fffff0U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 5U)) | 
                           ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                >> 8U)) << 4U)) & (
                                                   (0x3fffff0U 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                                       >> 6U)) 
                                                   | ((~ 
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                        >> 9U)) 
                                                      << 4U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xfff7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (8U & (((0xffffff8U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                      >> 4U) & ((~ 
                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                  >> 6U)) 
                                                << 3U)) 
                                    & ((0x7fffff8U 
                                        & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                           >> 5U)) 
                                       | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 7U)) 
                                          << 3U)))) 
                     | (0x7fffff8U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                       >> 5U) & ((~ 
                                                  (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                   >> 7U)) 
                                                 << 3U)))) 
                    | (((0xffffff8U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                       >> 4U)) | ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 6U)) 
                                                  << 3U)) 
                       & ((0x7fffff8U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 5U)) | 
                          ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                               >> 7U)) << 3U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xfffbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (4U & (((0x1ffffffcU & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                       >> 3U) & ((~ 
                                                  (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                   >> 4U)) 
                                                 << 2U)) 
                                     & ((0xffffffcU 
                                         & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 4U)) 
                                        | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                               >> 5U)) 
                                           << 2U)))) 
                     | (0xffffffcU & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                       >> 4U) & ((~ 
                                                  (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                   >> 5U)) 
                                                 << 2U)))) 
                    | (((0x1ffffffcU & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 3U)) | (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 4U)) 
                                                   << 2U)) 
                       & ((0xffffffcU & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 4U)) | 
                          ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                               >> 5U)) << 2U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xfffdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (2U & (((0x3ffffffeU & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                       >> 2U) & ((~ 
                                                  (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                   >> 2U)) 
                                                 << 1U)) 
                                     & ((0x1ffffffeU 
                                         & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 3U)) 
                                        | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                               >> 3U)) 
                                           << 1U)))) 
                     | (0x1ffffffeU & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 3U) & ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 3U)) 
                                                  << 1U)))) 
                    | (((0x3ffffffeU & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 2U)) | (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 2U)) 
                                                   << 1U)) 
                       & ((0x1ffffffeU & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 3U)) | 
                          ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                               >> 3U)) << 1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b 
        = ((0xfffeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)) 
           | (1U & (((((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                        >> 1U) & (~ vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U])) 
                      & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                          >> 2U) | (~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                       >> 1U)))) | 
                     ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                       >> 2U) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                    >> 1U)))) | (((
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                                   >> 1U) 
                                                  | (~ 
                                                     vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U])) 
                                                 & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                                     >> 2U) 
                                                    | (~ 
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                        >> 1U)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0x7fffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x8000U & (((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                              >> 0x1eU)) << 0xfU) & 
                         (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                          >> 0x10U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xbfffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x4000U & ((0x1c000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0xfU) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x1cU)) 
                                        << 0xeU)) & 
                                      ((0xc000U & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                                   >> 0x10U)) 
                                       | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 0x1dU)) 
                                          << 0xeU)))) 
                         | (0xc000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0x10U) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x1dU)) 
                                        << 0xeU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xdfffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x2000U & ((0x3e000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0xeU) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x1aU)) 
                                        << 0xdU)) & 
                                      ((0x1e000U & 
                                        (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xfU)) 
                                       | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 0x1bU)) 
                                          << 0xdU)))) 
                         | (0x1e000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xfU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x1bU)) 
                                         << 0xdU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xefffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x1000U & ((0x7f000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0xdU) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x18U)) 
                                        << 0xcU)) & 
                                      ((0x3f000U & 
                                        (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xeU)) 
                                       | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 0x19U)) 
                                          << 0xcU)))) 
                         | (0x3f000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xeU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x19U)) 
                                         << 0xcU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xf7ffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x800U & ((0xff800U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                       >> 0xcU) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0x16U)) 
                                                   << 0xbU)) 
                                     & ((0x7f800U & 
                                         (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                          >> 0xdU)) 
                                        | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                               >> 0x17U)) 
                                           << 0xbU)))) 
                        | (0x7f800U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0xdU) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x17U)) 
                                        << 0xbU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xfbffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x400U & ((0x1ffc00U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0xbU) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x14U)) 
                                        << 0xaU)) & 
                                      ((0xffc00U & 
                                        (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xcU)) 
                                       | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 0x15U)) 
                                          << 0xaU)))) 
                        | (0xffc00U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0xcU) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x15U)) 
                                        << 0xaU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xfdffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x200U & ((0x3ffe00U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 0xaU) & 
                                       ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                            >> 0x12U)) 
                                        << 9U)) & (
                                                   (0x1ffe00U 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                                       >> 0xbU)) 
                                                   | ((~ 
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                        >> 0x13U)) 
                                                      << 9U)))) 
                        | (0x1ffe00U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xbU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x13U)) 
                                         << 9U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xfeffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x100U & ((0x7fff00U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 9U) & ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 0x10U)) 
                                                  << 8U)) 
                                      & ((0x3fff00U 
                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                             >> 0xaU)) 
                                         | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 0x11U)) 
                                            << 8U)))) 
                        | (0x3fff00U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 0xaU) & 
                                        ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                             >> 0x11U)) 
                                         << 8U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xff7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x80U & ((0xffff80U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                       >> 8U) & ((~ 
                                                  (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                   >> 0xeU)) 
                                                 << 7U)) 
                                     & ((0x7fff80U 
                                         & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 9U)) 
                                        | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                               >> 0xfU)) 
                                           << 7U)))) 
                       | (0x7fff80U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 9U) & ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 0xfU)) 
                                                  << 7U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xffbfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x40U & ((0x1ffffc0U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 7U) & ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 0xcU)) 
                                                  << 6U)) 
                                      & ((0xffffc0U 
                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                             >> 8U)) 
                                         | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 0xdU)) 
                                            << 6U)))) 
                       | (0xffffc0U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 8U) & ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 0xdU)) 
                                                  << 6U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xffdfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x20U & ((0x3ffffe0U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 6U) & ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 0xaU)) 
                                                  << 5U)) 
                                      & ((0x1ffffe0U 
                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                             >> 7U)) 
                                         | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 0xbU)) 
                                            << 5U)))) 
                       | (0x1ffffe0U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 7U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 0xbU)) 
                                                   << 5U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xffefU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x10U & ((0x7fffff0U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 5U) & ((~ 
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                    >> 8U)) 
                                                  << 4U)) 
                                      & ((0x3fffff0U 
                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                             >> 6U)) 
                                         | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                >> 9U)) 
                                            << 4U)))) 
                       | (0x3fffff0U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                         >> 6U) & (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 9U)) 
                                                   << 4U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xfff7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (8U & ((0xffffff8U & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                     >> 4U) & ((~ (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                   >> 6U)) 
                                               << 3U)) 
                                   & ((0x7fffff8U & 
                                       (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                        >> 5U)) | (
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                     >> 7U)) 
                                                   << 3U)))) 
                    | (0x7fffff8U & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                      >> 5U) & ((~ 
                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                  >> 7U)) 
                                                << 3U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xfffbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (4U & ((0x1ffffffcU & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                      >> 3U) & ((~ 
                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                  >> 4U)) 
                                                << 2U)) 
                                    & ((0xffffffcU 
                                        & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                           >> 4U)) 
                                       | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 5U)) 
                                          << 2U)))) 
                    | (0xffffffcU & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                      >> 4U) & ((~ 
                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                  >> 5U)) 
                                                << 2U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xfffdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (2U & ((0x3ffffffeU & (((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                      >> 2U) & ((~ 
                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                  >> 2U)) 
                                                << 1U)) 
                                    & ((0x1ffffffeU 
                                        & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                           >> 3U)) 
                                       | ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                              >> 3U)) 
                                          << 1U)))) 
                    | (0x1ffffffeU & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                       >> 3U) & ((~ 
                                                  (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                   >> 3U)) 
                                                 << 1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0xfffeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (1U & ((((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                       >> 1U) & (~ vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U])) 
                     & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                         >> 2U) | (~ (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                      >> 1U)))) | (
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                                    >> 2U) 
                                                   & (~ 
                                                      (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                                                       >> 1U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a 
        = ((0x7fffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
           | (0x8000U & ((0xffff8000U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)) 
                         ^ (0xf8000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U] 
                                        >> 0xcU)))));
    taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
        = (0x7fffffffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                           >> 1U) & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U]));
    taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b 
        = (0x7fffffffU & ((~ ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                               << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                                            >> 1U))) 
                          & (~ vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__instruction_is_completing 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_issued_r) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U] 
              >> 0x1aU));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
                 ^ (0U != (0xfU & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
                 ^ (0U != (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
                 ^ (0U != (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
                 ^ (0U != (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
                 ^ (0U != (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input)) 
                 ^ (0U != (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
                 ^ (0U != (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index)))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
                 ^ (0U != (0xfU & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index)))));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__0__KET__.pop 
        = (IData)(((((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__inflight_count) 
                     >> 5U) & (~ ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out) 
                                  >> 6U))) & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo.full))));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_data_fifos__BRA__1__KET__.pop 
        = (IData)(((((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__inflight_count) 
                     >> 5U) & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out) 
                               >> 6U)) & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo.full))));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo.push 
        = (IData)(((((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__inflight_count) 
                     >> 5U) & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo.full))) 
                   & (~ (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__write_done 
        = ((((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__inflight_count) 
             >> 5U) & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_data_fifo.full))) 
           & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__burst_count) 
              == (0x1fU & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out) 
                           >> 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
                 ^ (0U != (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
                 ^ (0U != (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_conflict 
        = (0U != ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                           >> 2U)) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
                 ^ (0U != (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
                 ^ (0U != (0x1fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input)) 
                 ^ (0U != (0x1fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback_input)) 
                 ^ (0U != (0x1fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
                 ^ (0U != (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[2U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux
            [2U]) | (0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[2U] 
        = ((0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux
            [2U]) | (1U & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index_mux[2U] 
        = (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                    >> 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback_input)) 
                 ^ (0U != (0x1fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback 
        = (1U & ((~ VL_REDXOR_2(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input)) 
                 ^ (0U != (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[2U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux
            [2U]) | (0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[2U] 
        = ((0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux
            [2U]) | (1U & vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index_mux[2U] 
        = (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                    >> 0xdU));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__return_push = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__return_push 
        = (((~ ((IData)(1U) << (1U & (IData)((taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                              >> 0x22U))))) 
            & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__return_push)) 
           | (3U & ((1U & ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__inflight_count) 
                           >> 4U)) << (1U & (IData)(
                                                    (taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                     >> 0x22U))))));
    vlSelf->ddr_axi_araddr = ((IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                       >> 0x10U)) << 4U);
    vlSelf->ddr_axi_arid = (7U & (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out));
    vlSelf->ddr_axi_arlen = (0x1fU & (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                              >> 3U)));
    vlSelf->ddr_axi_awaddr = ((IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                       >> 0xeU)) << 2U);
    taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
        = (((IData)((((QData)((IData)(vlSelf->ddr_axi_rdata)) 
                      << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out)))) 
            << 5U) | (0x1fU & (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                       >> 3U))));
    taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
        = (((IData)((((QData)((IData)(vlSelf->ddr_axi_rdata)) 
                      << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out)))) 
            >> 0x1bU) | ((IData)(((((QData)((IData)(vlSelf->ddr_axi_rdata)) 
                                    << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out))) 
                                  >> 0x20U)) << 5U));
    taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
        = ((IData)(((((QData)((IData)(vlSelf->ddr_axi_rdata)) 
                      << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out))) 
                    >> 0x20U)) >> 0x1bU);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__read_modify_write 
        = (1U & (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                         >> 8U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_is_float 
        = (((((((1U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                 >> 2U))) | (9U == 
                                             (0x1fU 
                                              & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                                 >> 2U)))) 
               | (0x10U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                     >> 2U)))) | (0x11U 
                                                  == 
                                                  (0x1fU 
                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                                      >> 2U)))) 
             | (0x12U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                   >> 2U)))) | (0x13U 
                                                == 
                                                (0x1fU 
                                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                                    >> 2U)))) 
           | (0x14U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                 >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_wb2_int 
        = (IData)(((0x50U == (0x7cU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction)) 
                   & (((0x61U == (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                  >> 0x19U)) | (0x51U 
                                                == 
                                                (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                                 >> 0x19U))) 
                      | (0x71U == (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                   >> 0x19U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_accu_fcsr 
        = (((((((((((((((((((0x2000043U == (0x600007fU 
                                            & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction)) 
                            | (0x2000047U == (0x600007fU 
                                              & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                           | (0x200004bU == (0x600007fU 
                                             & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                          | (0x200004fU == (0x600007fU 
                                            & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                         | (0x2000043U == (0x600007fU 
                                           & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                        | (0x2000053U == (0xfe00007fU 
                                          & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                       | (0xa000053U == (0xfe00007fU 
                                         & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                      | (0x12000053U == (0xfe00007fU 
                                         & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                     | (0x1a000053U == (0xfe00007fU 
                                        & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                    | (0x5a000053U == (0xfff0007fU 
                                       & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                   | (0x2a000053U == (0xfe00707fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                  | (0x2a001053U == (0xfe00707fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                 | (0x40100053U == (0xfff0007fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
                | (0x42000053U == (0xfff0007fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
               | (0xa2002053U == (0xfe00707fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
              | (0xa2001053U == (0xfe00707fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
             | (0xa2000053U == (0xfe00707fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
            | (0xc2000053U == (0xfff0007fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction))) 
           | (0xc2100053U == (0xfff0007fU & vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction)));
    taiga_sim__DOT__cpu__DOT__fetch_block__DOT__is_branch_or_jump 
        = (((0x1bU == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                >> 2U))) | (0x19U == 
                                            (0x1fU 
                                             & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                                >> 2U)))) 
           | (0x18U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction 
                                 >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__new_quotient_bits 
        = ((2U & ((~ (IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x_overflow)) 
                  << 1U)) | (1U & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_1x_overflow))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U] 
        = ((0xfeffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U]) 
           | (0x1000000U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                            << 0xcU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U] 
        = ((0xfffff7ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U]) 
           | (0x800U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                        >> 1U)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_overflow_norm 
        = (1U & (((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                   ? (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm_right_shift)
                   : (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm_left_shift)) 
                 >> 0xbU));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm 
        = (0x7ffU & ((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                      ? (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm_right_shift)
                      : (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm_left_shift)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U] 
        = ((0xff000fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U]) 
           | (0xfffff000U & (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm) 
                              << 0xdU) | ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_overflow_norm) 
                                          << 0xcU))));
    __Vtemp_hf725ef03__0[4U] = ((0x40000000U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                                                << 0x1bU)) 
                                | ((0x20000000U & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                                                   << 0x1bU)) 
                                   | ((0x10000000U 
                                       & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                                          << 0x1bU)) 
                                      | (((IData)((0xfffffffffffffULL 
                                                   & (((QData)((IData)(
                                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U])) 
                                                       << 0x33U) 
                                                      | (((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[5U])) 
                                                          << 0x13U) 
                                                         | ((QData)((IData)(
                                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U])) 
                                                            >> 0xdU))))) 
                                          >> 0x18U) 
                                         | ((IData)(
                                                    ((0xfffffffffffffULL 
                                                      & (((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U])) 
                                                          << 0x33U) 
                                                         | (((QData)((IData)(
                                                                             vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[5U])) 
                                                             << 0x13U) 
                                                            | ((QData)((IData)(
                                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U])) 
                                                               >> 0xdU)))) 
                                                     >> 0x20U)) 
                                            << 8U)))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[0U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[1U] 
            << 7U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                      >> 0x19U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[1U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[2U] 
            << 7U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[1U] 
                      >> 0x19U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[2U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[3U] 
            << 7U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[2U] 
                      >> 0x19U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[3U] 
        = (((IData)((0xfffffffffffffULL & (((QData)((IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U])) 
                                            << 0x33U) 
                                           | (((QData)((IData)(
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[5U])) 
                                               << 0x13U) 
                                              | ((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U])) 
                                                 >> 0xdU))))) 
            << 8U) | (0xffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                                << 7U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[3U] 
                                          >> 0x19U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[4U] 
        = __Vtemp_hf725ef03__0[4U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__in[0U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[0U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__in[1U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[1U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__in[2U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[2U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__in[3U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[3U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__in[4U] 
        = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[4U];
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i = 0x9eU;
    while (VL_LTES_III(32, 0U, __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT____Vlvbound_he380f72e__0 
            = ((0x9eU >= (0xffU & ((IData)(0x9eU) - __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i))) 
               & (__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__in[
                  (7U & (((IData)(0x9eU) - __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i) 
                         >> 5U))] >> (0x1fU & ((IData)(0x9eU) 
                                               - __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i))));
        if (VL_LIKELY((0x9eU >= (0xffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i)))) {
            vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout[(7U 
                                                                                & (__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i 
                                                                                >> 5U))] 
                = (((~ ((IData)(1U) << (0x1fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i))) 
                    & vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout[
                    (7U & (__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i 
                           >> 5U))]) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT____Vlvbound_he380f72e__0) 
                                        << (0x1fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i)));
        }
        __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i 
            = (__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__unnamedblk1__DOT__i 
               - (IData)(1U));
    }
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[0U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout[0U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[1U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout[1U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[2U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout[2U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[3U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout[3U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[4U] 
        = vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout[4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[0U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[0U]) 
           | (((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[0U]
                : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[0U]) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[1U] 
        = ((((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
              ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[0U]
              : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[0U]) 
            >> 0x1fU) | (((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                           ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[1U]
                           : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[1U]) 
                         << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[2U] 
        = ((((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
              ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[1U]
              : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[1U]) 
            >> 0x1fU) | (((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                           ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[2U]
                           : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[2U]) 
                         << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[3U] 
        = ((((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
              ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[2U]
              : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[2U]) 
            >> 0x1fU) | (((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                           ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[3U]
                           : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[3U]) 
                         << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[4U] 
        = ((((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
              ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[3U]
              : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[3U]) 
            >> 0x1fU) | (((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                           ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[4U]
                           : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[4U]) 
                         << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U] 
        = ((0xfffff800U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U]) 
           | (((1U & ((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                       ? ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                           << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                        >> 1U)) : ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_less_than_left_shift_amt)
                                                    ? 
                                                   ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                                                     << 0x1fU) 
                                                    | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                                                       >> 1U))
                                                    : 
                                                   ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                                     << 0x12U) 
                                                    | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                                       >> 0xeU))))) 
               | (((0x1000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                    ? taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__right[4U]
                    : taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__left[4U]) 
                  >> 0x1fU)) | (0x7feU & ((0x1000U 
                                           & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U])
                                           ? ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                               << 0x1fU) 
                                              | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                                 >> 1U))
                                           : ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_less_than_left_shift_amt)
                                               ? ((
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                                                   << 0x1fU) 
                                                  | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                                                     >> 1U))
                                               : ((
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                                   << 0x12U) 
                                                  | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                                     >> 0xeU)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[0U] 
        = ((0xfffffffeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[0U]) 
           | (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_overflow_norm) 
               | (0x7ffU == (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__expo_norm))) 
              & (0U != (0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[0U] 
                                  >> 0xeU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U] 
        = ((0x1ffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[5U]) 
           | (0xfe000000U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                             << 0x15U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet[6U] 
        = (0x1fU & ((0x10U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                              >> 9U)) | ((0xeU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                                                  >> 0xdU)) 
                                         | (1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[4U] 
                                                  >> 0xbU)))));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.grantee_i 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes
        [vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__state];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[0U] 
        = (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_if_overflow);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[1U] 
        = (IData)((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__result_if_overflow 
                   >> 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[2U] 
        = ((0xffffffbfU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet[2U]) 
           | ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vcellout__round__roundup) 
              << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__commit 
        = (((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__csr_unit_block__retire_ids
             [0U] == (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__2__KET__.id)) 
            & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__busy)) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__commit_in_progress)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_ids[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_ids
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_ids[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_ids
        [1U];
    vlSelf->load_store_idle = vlSelf->taiga_sim__DOT__cpu__DOT__load_store_idle;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_port_valid[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_port_valid
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_port_valid[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_port_valid
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches))
            ? 1U : 0U);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way) 
                 | ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches))
                     ? 0U : 0U)));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment 
        = ((1U & (IData)((taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr 
                          >> 3U))) ? vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb
           [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest]
            : vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_issue
           [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest]);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data 
        = ((0xffffff00U & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data) 
           | (0xffU & taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data 
        = ((0xffff00ffU & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data) 
           | (0xff00U & (((1U == (3U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                >> 0xbU))))
                           ? taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment
                           : (taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment 
                              >> 8U)) << 8U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data 
        = ((0xff00ffffU & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data) 
           | (0xff0000U & (((2U == (3U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                  >> 0xbU))))
                             ? taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment
                             : (taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment 
                                >> 0x10U)) << 0x10U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data 
        = ((0xffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data) 
           | (((2U == (3U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                     >> 0xbU)))) ? 
               (taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment 
                >> 8U) : ((3U == (3U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                >> 0xbU))))
                           ? taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment
                           : (taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__data_for_alignment 
                              >> 0x18U))) << 0x18U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__early_terminate 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_QNaN) 
            | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_inf)) 
           | ((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_QNaN)) 
              & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_zero) 
                 | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_inf))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__special_case_results[0U] 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_inf)
            ? (0x7ff0000000000000ULL | ((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_sign
                                                        [0U])) 
                                        << 0x3fU)) : 
           ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_QNaN)
             ? 0x7ff8000000000000ULL : ((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_sign
                                                        [0U])) 
                                        << 0x3fU)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div_issue.new_request 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__1__KET__.new_request) 
           & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U] 
                 >> 0x14U)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_issue.new_request 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__1__KET__.new_request) 
           & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U] 
              >> 0x14U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[0U] 
        = ((0xfffff001U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[0U]) 
           | (0xffeU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[1U] 
                        >> 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[0U] 
        = ((0xfff00fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[0U]) 
           | (0xfffff000U & (((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__1__KET__.id) 
                              << 0x11U) | ((0x10000U 
                                            & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[1U] 
                                               << 1U)) 
                                           | (0xf000U 
                                              & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U] 
                                                 << 8U))))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__expo_normalized 
        = (0xfffU & (((0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U] 
                                 >> 4U)) + (1U & (~ 
                                                  (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[0U] 
                                                   >> 0x17U)))) 
                     - (0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[1U] 
                                  >> 3U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[2U] 
        = ((0x7fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[2U]) 
           | (((IData)(((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap)
                         ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped
                         : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped)) 
               << 9U) | (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                           [0U] | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                           [1U]) << 8U) | (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap)
                                             ? (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_hidden_bit_pre_normalized_swapped)
                                             : (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_hidden_bit_pre_normalized_swapped)) 
                                           << 7U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[3U] 
        = (((0x7fU & ((IData)(((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap)
                                ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped
                                : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped)) 
                      >> 0x17U)) | ((0x7fU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                               [0U] 
                                               | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN
                                               [1U]) 
                                              >> 0x18U)) 
                                    | (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap)
                                         ? (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_hidden_bit_pre_normalized_swapped)
                                         : (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_hidden_bit_pre_normalized_swapped)) 
                                       >> 0x19U))) 
           | ((0x180U & ((IData)(((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap)
                                   ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped
                                   : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped)) 
                         >> 0x17U)) | ((IData)((((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap)
                                                  ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped
                                                  : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped) 
                                                >> 0x20U)) 
                                       << 9U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
        = ((0xfffffe00U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U]) 
           | ((0x7fU & ((IData)((((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap)
                                   ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped
                                   : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped) 
                                 >> 0x20U)) >> 0x17U)) 
              | (0x180U & ((IData)((((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_output_swap)
                                      ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped
                                      : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped) 
                                    >> 0x20U)) >> 0x17U))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__mul_issue.new_request 
        = ((IData)((0U != (0xa000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U]))) 
           & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__0__KET__.new_request));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs_fifo.potential_push 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
            >> 0xeU) & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__debug_fp_unit_issue__BRA__0__KET__.new_request));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_frac[0U] 
        = (((QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                                   >> 8U)))) << 0x34U) 
           | (0xfffffffffffffULL & (((QData)((IData)(
                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0x10U])) 
                                     << 0x33U) | (((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xfU])) 
                                                   << 0x13U) 
                                                  | ((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU])) 
                                                     >> 0xdU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_frac[0U] 
        = (((QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                                   >> 7U)))) << 0x34U) 
           | (0xfffffffffffffULL & (((QData)((IData)(
                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU])) 
                                     << 0x33U) | (((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xdU])) 
                                                   << 0x13U) 
                                                  | ((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xcU])) 
                                                     >> 0xdU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode[0U] 
        = (0x7fU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
                    >> 0x13U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__instruction[0U] 
        = (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
                 >> 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case[0U] 
        = (0xfU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
                   >> 0x1aU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3[0U] 
        = (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xcU])) 
            << 0x33U) | (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xbU])) 
                          << 0x13U) | ((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xaU])) 
                                       >> 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit[0U] 
        = (1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                 >> 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm[0U] 
        = (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
                 >> 0x10U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_sign[0U] 
        = (1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0x10U] 
                 >> 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_sign[0U] 
        = (1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU] 
                 >> 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_expo[0U] 
        = (0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0x10U] 
                     >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_expo[0U] 
        = (0x7ffU & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU] 
                       << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU] 
                                    >> 1U)) + (1U & 
                                               (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                                                >> 0xaU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt[0U] 
        = (0x7ffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xaU] 
                      << 9U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                                >> 0x17U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation[0U] 
        = (((((IData)((6U == (6U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U]))) 
              | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                  >> 5U) & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
                            >> 0x1eU))) & (0x7ff8000000000000ULL 
                                           != (((QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU])) 
                                                << 0x33U) 
                                               | (((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xdU])) 
                                                   << 0x13U) 
                                                  | ((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xcU])) 
                                                     >> 0xdU))))) 
            | (0x7ff4000000000000ULL == (((QData)((IData)(
                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0x10U])) 
                                          << 0x33U) 
                                         | (((QData)((IData)(
                                                             vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xfU])) 
                                             << 0x13U) 
                                            | ((QData)((IData)(
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU])) 
                                               >> 0xdU))))) 
           | (0x7ff4000000000000ULL == (((QData)((IData)(
                                                         vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xeU])) 
                                         << 0x33U) 
                                        | (((QData)((IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xdU])) 
                                            << 0x13U) 
                                           | ((QData)((IData)(
                                                              vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[0xcU])) 
                                              >> 0xdU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr
        [2U];
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data 
        = ((0xffff0000U & taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_muxed_load_data) 
           | (0xffffU & ((0x80U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out))
                          ? (taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_muxed_load_data 
                             >> 0x10U) : taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_muxed_load_data)));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data 
        = ((0xffffff00U & taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data) 
           | (0xffU & ((0x40U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out))
                        ? (taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data 
                           >> 8U) : taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel[0U] 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom) 
                 >> vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done
                 [0U]));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet[0U] 
        = ((0xeffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
            [0U]) | ((QData)((IData)((0U != vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
                                      [0U]))) << 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet[1U] 
        = ((0xeffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
            [1U]) | ((QData)((IData)((0U != vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
                                      [1U]))) << 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel[1U] 
        = ((0x5fU >= (0x7fU & ((IData)(3U) * (0x1fU 
                                              & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
                                              [1U]))))
            ? (7U & (((0U == (0x1fU & ((IData)(3U) 
                                       * (0x1fU & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
                                          [1U])))) ? 0U
                       : (vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom[
                          (((IData)(2U) + (0x7fU & 
                                           ((IData)(3U) 
                                            * (0x1fU 
                                               & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
                                               [1U])))) 
                           >> 5U)] << ((IData)(0x20U) 
                                       - (0x1fU & ((IData)(3U) 
                                                   * 
                                                   (0x1fU 
                                                    & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
                                                    [1U])))))) 
                     | (vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom[
                        (3U & (((IData)(3U) * (0x1fU 
                                               & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
                                               [1U])) 
                               >> 5U))] >> (0x1fU & 
                                            ((IData)(3U) 
                                             * (0x1fU 
                                                & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done
                                                [1U]))))))
            : 0U);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rs1_link 
        = ((1U == (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                   >> 0x1bU)) | (5U == (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                        >> 0x1bU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rd_link 
        = ((1U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                            >> 0x13U))) | (5U == (0x1fU 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                                     >> 0x13U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match 
        = ((0U == (0xfffU & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))
            ? (0xfeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match))
            : ((1U == (0xfffU & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))
                ? (0xfdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match))
                : ((0x102U == (0xfffU & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))
                    ? (0xf7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match))
                    : ((0x302U == (0xfffU & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))
                        ? (0xefU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match))
                        : ((0x120U == (0xfe0U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))
                            ? (0xdfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match))
                            : 0U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__uses_rs1 
        = (((((0x10U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                  >> 0xeU))) | (0x11U 
                                                == 
                                                (0x1fU 
                                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                                    >> 0xeU)))) 
             | (0x12U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                   >> 0xeU)))) | (0x13U 
                                                  == 
                                                  (0x1fU 
                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                                      >> 0xeU)))) 
           | (IData)(((0x50000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                      & (((((((((((1U == (0x7fU & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                                   >> 5U))) 
                                  | (5U == (0x7fU & 
                                            (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                             >> 5U)))) 
                                 | (9U == (0x7fU & 
                                           (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                            >> 5U)))) 
                                | (0xdU == (0x7fU & 
                                            (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                             >> 5U)))) 
                               | (0x2dU == (0x7fU & 
                                            (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                             >> 5U)))) 
                              | (0x11U == (0x7fU & 
                                           (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                            >> 5U)))) 
                             | (0x15U == (0x7fU & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                                   >> 5U)))) 
                            | (0x51U == (0x7fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                                  >> 5U)))) 
                           | (0x20U == (0x7fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                                 >> 5U)))) 
                          | (0x71U == (0x7fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                                >> 5U)))) 
                         | (0x61U == (0x7fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                               >> 5U)))))));
    __Vtableidx1 = ((0xe0U & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                              >> 0x13U)) | (0x1fU & 
                                            (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                             >> 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_op 
        = Vtaiga_sim__ConstPool__TABLE_he47736a6_0[__Vtableidx1];
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_ifence 
        = (IData)((0x100c000U == (0x107c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fence 
        = (IData)((0xc000U == (0x107c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed 
        = ((0xeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed)) 
           | ((4U == (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                            >> 0x10U))) | (IData)((
                                                   (0x50000U 
                                                    == 
                                                    (0x7c000U 
                                                     & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                                                   & (((9U 
                                                        == 
                                                        (0x7fU 
                                                         & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                                            >> 5U))) 
                                                       | (1U 
                                                          == 
                                                          (0x7fU 
                                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                                              >> 5U)))) 
                                                      | (5U 
                                                         == 
                                                         (0x7fU 
                                                          & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                                             >> 5U))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed 
        = ((0xdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed)) 
           | ((IData)(((0x50000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                       & (0x1a0U == (0x1e0U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U])))) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_i2f 
        = (IData)(((0x50000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                   & (0xd20U == (0xfe0U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_f2i 
        = (IData)(((0x50000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                   & (0xc20U == (0xfe0U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_class 
        = (IData)(((0x50000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                   & (0xe20U == (0xfe0U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fcmp 
        = (IData)(((0x50000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                   & (0xa20U == (0xfe0U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_minmax 
        = (IData)(((0x50000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                   & (0x2a0U == (0xfe0U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_sign_inj 
        = (IData)(((0x50000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                   & (0x220U == (0xfe0U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]))));
    taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_csr 
        = (IData)(((0x70000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                   & (0U != (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                   >> 0x18U)))));
    taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__mult_div_op 
        = (IData)(((0x30000U == (0x7c000U & vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U])) 
                   & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                      >> 5U)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.phys_rd_addr 
        = ((0U != (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                            >> 0x13U))) ? (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list.data_out)
            : 0U);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_addr[1U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
           >> 0x1bU);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_addr[2U] 
        = (0x1fU & vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index_mux[0U] 
        = (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                    >> 0x13U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index_mux[0U] 
        = (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                    >> 0x13U));
    TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface__DOT__rs_addr 
        = ((0x7c00U & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                       << 3U)) | (0x3ffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__decode[1U] 
                                             << 5U) 
                                            | (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                               >> 0x1bU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed 
        = ((0x7dfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed)) 
           | ((((0x18U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                    >> 0xeU))) | (0x1bU 
                                                  == 
                                                  (0x1fU 
                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                                      >> 0xeU)))) 
               | (0x19U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                     >> 0xeU)))) << 5U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__feq 
        = (1U & ((IData)((0x88000U == (0x88000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[2U]))) 
                 | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__sign_equ) 
                     & (~ (IData)((0U != (0x7ffU & 
                                          (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                             << 0x15U) 
                                            | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                               >> 0xbU)) 
                                           ^ ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[4U] 
                                               << 0x15U) 
                                              | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[4U] 
                                                 >> 0xbU)))))))) 
                    & (~ (IData)((0U != (0xfffffffffffffULL 
                                         & ((((QData)((IData)(
                                                              vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U])) 
                                              << 0x29U) 
                                             | (((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[5U])) 
                                                 << 9U) 
                                                | ((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[4U])) 
                                                   >> 0x17U))) 
                                            ^ (((QData)((IData)(
                                                                vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[4U])) 
                                                << 0x29U) 
                                               | (((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[3U])) 
                                                   << 9U) 
                                                  | ((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[2U])) 
                                                     >> 0x17U)))))))))));
    vlSelf->taiga_sim__DOT__l2_arb__DOT____Vcellout__reserv__abort 
        = ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_sc) 
           & ((~ ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation) 
                  >> (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_id))) 
              | (((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation) 
                  >> (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_id)) 
                 & (~ ((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match) 
                       >> (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_id))))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__i = 0U;
    {
        while (VL_GTS_III(32, 0x34U, taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__i)) {
            if (((0x37U >= (0x3fU & ((IData)(0x37U) 
                                     - taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__i))) 
                 & (IData)((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt.radicand 
                            >> (0x3fU & ((IData)(0x37U) 
                                         - taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__i)))))) {
                goto __Vlabel1;
            }
            taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__i 
                = ((IData)(1U) + taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__i);
        }
        __Vlabel1: ;
    }
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__radicand_clz 
        = (0x3fU & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__i);
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__early_terminate 
        = (1U & ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_inf) 
                   | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U] 
                      >> 0xcU)) | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_QNaN)) 
                 | (((0x3ffU == (0x7ffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo))) 
                     & (~ (IData)((0U != (0xfffffffffffffULL 
                                          & (((QData)((IData)(
                                                              vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[2U])) 
                                              << 0x2cU) 
                                             | (((QData)((IData)(
                                                                 vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[1U])) 
                                                 << 0xcU) 
                                                | ((QData)((IData)(
                                                                   vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U])) 
                                                   >> 0x14U)))))))) 
                    & (~ (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[2U] 
                          >> 0x13U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal[0U] 
        = ((0xbU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal
            [0U]) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                      [0U] ? ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__right_shift) 
                              & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case
                                 [0U])) : (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb.subnormal)) 
                     << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift[0U] 
        = ((0xbU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift
            [0U]) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                      [0U] ? ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__right_shift) 
                              & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case
                                 [0U])) : (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb.right_shift)) 
                     << 2U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo 
        = (0xfffU & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__right_shift)
                      ? (0x1fffU & (- vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate
                                    [1U])) : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate
                     [1U]));
    if (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
        [0U]) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_fflags[0U][2U] 
            = ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_by_zero) 
               << 3U);
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd[0U][2U] 
            = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case
               [0U] ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__special_case_results
               [0U] : (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_sign
                                        [0U])) << 0x3fU) 
                       | (((QData)((IData)((0x7ffU 
                                            & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo)))) 
                           << 0x34U) | (0xfffffffffffffULL 
                                        & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.quotient 
                                           >> 2U)))));
    } else {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_fflags[0U][2U] 
            = (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__invalid_operation) 
                << 4U) | (0U != vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__grs
                          [0U]));
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd[0U][2U] 
            = ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__early_terminate)
                ? ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_QNaN)
                    ? 0x7ff8000000000000ULL : ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_inf)
                                                ? 0x7ff0000000000000ULL
                                                : (
                                                   (0x1000U 
                                                    & vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[0U])
                                                    ? 
                                                   ((QData)((IData)(
                                                                    (1U 
                                                                     & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U] 
                                                                        >> 0xfU)))) 
                                                    << 0x3fU)
                                                    : 0x3ff0000000000000ULL)))
                : (((QData)((IData)((1U & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__input_fifo.data_out[2U] 
                                           >> 0x13U)))) 
                    << 0x3fU) | (((QData)((IData)((0x7ffU 
                                                   & ((IData)(0x3ffU) 
                                                      + 
                                                      (0xfffU 
                                                       & ((0x800U 
                                                           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo))
                                                           ? 
                                                          (- 
                                                           (0x7ffU 
                                                            & (((0x800U 
                                                                 & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo))
                                                                 ? 
                                                                (- (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo))
                                                                 : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo)) 
                                                               >> 1U)))
                                                           : 
                                                          (0x7ffU 
                                                           & (((0x800U 
                                                                & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo))
                                                                ? 
                                                               (- (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo))
                                                                : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo)) 
                                                              >> 1U)))))))) 
                                  << 0x34U) | (0xfffffffffffffULL 
                                               & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__result_frac
                                               [0U]))));
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact[0U] 
        = (0U != (((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[0U] 
                    | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[1U]) 
                   | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[2U]) 
                  | (0xffU & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm[0U] 
        = (7U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                 >> 5U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs1_expo 
        = ((0x800U & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U]) 
           | (0x7ffU & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[8U] 
                        >> 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff[0U] 
        = (0xfffU & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U] 
                     >> 8U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs2_sign 
        = (1U & ((0x100000U & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U])
                  ? (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U] 
                     >> 0xcU) : (~ (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U] 
                                    >> 0xcU))));
    if ((0x200000U & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U])) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac[0U] 
            = (((QData)((IData)((1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                                       >> 8U)))) << 0x35U) 
               | (((QData)((IData)((1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                                          >> 0xaU)))) 
                   << 0x34U) | (0xfffffffffffffULL 
                                & (((QData)((IData)(
                                                    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U])) 
                                    << 0x33U) | (((QData)((IData)(
                                                                  taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[5U])) 
                                                  << 0x13U) 
                                                 | ((QData)((IData)(
                                                                    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U])) 
                                                    >> 0xdU))))));
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[0U][0U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[0U][1U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[0U][2U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[0U][3U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac[0U] 
            = (((QData)((IData)((1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                                       >> 9U)))) << 0x35U) 
               | (((QData)((IData)((1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                                          >> 0xcU)))) 
                   << 0x34U) | (0xfffffffffffffULL 
                                & (((QData)((IData)(
                                                    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[8U])) 
                                    << 0x33U) | (((QData)((IData)(
                                                                  taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[7U])) 
                                                  << 0x13U) 
                                                 | ((QData)((IData)(
                                                                    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U])) 
                                                    >> 0xdU))))));
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[0U][0U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[0U][1U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[0U][2U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[2U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[0U][3U] 
            = (0xffU & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U]);
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo[0U] 
            = (0x7ffU & ((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U] 
                          << 0x1fU) | (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U] 
                                       >> 1U)));
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo_overflow[0U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_sign[0U] 
            = (1U & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs2_sign));
    } else {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac[0U] 
            = (((QData)((IData)((1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                                       >> 9U)))) << 0x35U) 
               | (((QData)((IData)((1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                                          >> 0xcU)))) 
                   << 0x34U) | (0xfffffffffffffULL 
                                & (((QData)((IData)(
                                                    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[8U])) 
                                    << 0x33U) | (((QData)((IData)(
                                                                  taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[7U])) 
                                                  << 0x13U) 
                                                 | ((QData)((IData)(
                                                                    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U])) 
                                                    >> 0xdU))))));
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[0U][0U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[0U][1U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[0U][2U] 
            = taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[2U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[0U][3U] 
            = (0xffU & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U]);
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac[0U] 
            = (((QData)((IData)((1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                                       >> 8U)))) << 0x35U) 
               | (((QData)((IData)((1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U] 
                                          >> 0xaU)))) 
                   << 0x34U) | (0xfffffffffffffULL 
                                & (((QData)((IData)(
                                                    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[6U])) 
                                    << 0x33U) | (((QData)((IData)(
                                                                  taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[5U])) 
                                                  << 0x13U) 
                                                 | ((QData)((IData)(
                                                                    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[4U])) 
                                                    >> 0xdU))))));
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[0U][0U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[0U][1U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[0U][2U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[0U][3U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo[0U] 
            = (0x7ffU & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs1_expo));
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo_overflow[0U] 
            = (1U & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs1_expo) 
                     >> 0xbU));
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_sign[0U] 
            = (1U & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[8U] 
                     >> 0xcU));
    }
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__overflowExp 
        = (1U & (((0x1ffU == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs)) 
                  & (0x3ffU == (0x3ffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[4U] 
                                           << 2U) | 
                                          (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[3U] 
                                           >> 0x1eU))))) 
                 | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
                    >> 8U)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_out 
        = (0xfffffffffffffULL & ((0xfffffffffffffULL 
                                  & ((((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[3U])) 
                                       << 0x37U) | 
                                      (((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[3U])) 
                                        << 0x17U) | 
                                       ((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U])) 
                                        >> 9U))) + (QData)((IData)(
                                                                   (1U 
                                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
                                                                       >> 6U)))))) 
                                 >> (0x1ffU == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs))));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz 
        = ((0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)) 
           | (0x80U & ((~ (IData)((0U != (0xfU & taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend)))) 
                       << 7U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                >> 1U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz 
        = ((0xbfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)) 
           | (0x40U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                                                  >> 4U))))) 
                       << 6U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                >> 5U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz 
        = ((0xdfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)) 
           | (0x20U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                                                  >> 8U))))) 
                       << 5U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                >> 9U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz 
        = ((0xefU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)) 
           | (0x10U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                                                  >> 0xcU))))) 
                       << 4U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                >> 0xdU))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz 
        = ((0xf7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)) 
           | (8U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                                               >> 0x10U))))) 
                    << 3U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                >> 0x11U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz 
        = ((0xfbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)) 
           | (4U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                                               >> 0x14U))))) 
                    << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                >> 0x15U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz 
        = ((0xfdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)) 
           | (2U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                                               >> 0x18U))))) 
                    << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                >> 0x19U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz 
        = ((0xfeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)) 
           | (1U & (~ (IData)((0U != (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
                                      >> 0x1cU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table
        [(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend 
          >> 0x1dU)];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ 
        = ((0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ)) 
           | ((IData)((0xfU == (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)))) 
              << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ 
        = ((0x17U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ)) 
           | (((0x10U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ))
                ? (3U == (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz) 
                                >> 4U))) : (3U == (3U 
                                                   & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)))) 
              << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ 
        = ((0x1bU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ)) 
           | (4U & (((((IData)((1U == (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)))) 
                       | (IData)((7U == (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz))))) 
                      | (IData)((0x1fU == (0x3fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz))))) 
                     | (0x7fU == (0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz)))) 
                    << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__upper_lower[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz
        [(1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__upper_lower[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz
        [(2U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz) 
                      >> 2U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__upper_lower[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz
        [(4U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz) 
                      >> 4U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__upper_lower[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz
        [(6U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz) 
                      >> 6U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ 
        = ((0x1cU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ)) 
           | vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__upper_lower
           [(3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ) 
                   >> 3U))]);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz 
        = ((0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)) 
           | (0x80U & ((~ (IData)((0U != (0xfU & taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor)))) 
                       << 7U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                >> 1U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz 
        = ((0xbfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)) 
           | (0x40U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                                                  >> 4U))))) 
                       << 6U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                >> 5U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz 
        = ((0xdfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)) 
           | (0x20U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                                                  >> 8U))))) 
                       << 5U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                >> 9U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz 
        = ((0xefU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)) 
           | (0x10U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                                                  >> 0xcU))))) 
                       << 4U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                >> 0xdU))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz 
        = ((0xf7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)) 
           | (8U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                                               >> 0x10U))))) 
                    << 3U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                >> 0x11U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz 
        = ((0xfbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)) 
           | (4U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                                               >> 0x14U))))) 
                    << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                >> 0x15U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz 
        = ((0xfdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)) 
           | (2U & ((~ (IData)((0U != (0xfU & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                                               >> 0x18U))))) 
                    << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table
        [(7U & (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                >> 0x19U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz 
        = ((0xfeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)) 
           | (1U & (~ (IData)((0U != (taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
                                      >> 0x1cU))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table
        [(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor 
          >> 0x1dU)];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ 
        = ((0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ)) 
           | ((IData)((0xfU == (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)))) 
              << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ 
        = ((0x17U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ)) 
           | (((0x10U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ))
                ? (3U == (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz) 
                                >> 4U))) : (3U == (3U 
                                                   & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)))) 
              << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ 
        = ((0x1bU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ)) 
           | (4U & (((((IData)((1U == (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)))) 
                       | (IData)((7U == (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz))))) 
                      | (IData)((0x1fU == (0x3fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz))))) 
                     | (0x7fU == (0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz)))) 
                    << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__upper_lower[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz
        [(1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__upper_lower[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz
        [(2U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz) 
                      >> 2U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__upper_lower[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz
        [(4U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz) 
                      >> 4U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__upper_lower[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz
        [(6U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz) 
                      >> 6U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ 
        = ((0x1cU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ)) 
           | vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__upper_lower
           [(3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ) 
                   >> 3U))]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__expo_diff 
        = (0xfffU & (((0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U] 
                                 >> 0x14U)) + (1U & 
                                               (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit
                                                [0U]))) 
                     - ((0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U] 
                                   >> 0x14U)) + (1U 
                                                 & (~ 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit
                                                    [1U])))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal[0U] 
        = (1U & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit
                 [0U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal[1U] 
        = (1U & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit
                 [1U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal[2U] 
        = (1U & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit
                 [2U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac 
        = (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit
                            [0U])) << 0x34U) | (0xfffffffffffffULL 
                                                & (((QData)((IData)(
                                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[6U])) 
                                                    << 0x20U) 
                                                   | (QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[5U])))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac 
        = (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit
                            [1U])) << 0x34U) | (0xfffffffffffffULL 
                                                & (((QData)((IData)(
                                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[4U])) 
                                                    << 0x20U) 
                                                   | (QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet[3U])))));
    taiga_sim__DOT__cpu__DOT__alu_unit_block__DOT__add_sub_result 
        = (0x1ffffffffULL & (((1ULL | (0x3fffffffeULL 
                                       & (((0U == (3U 
                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                                      >> 8U)))
                                            ? ((((QData)((IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U])) 
                                                 << 0x33U) 
                                                | (((QData)((IData)(
                                                                    vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U])) 
                                                    << 0x13U) 
                                                   | ((QData)((IData)(
                                                                      vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                      >> 0xdU))) 
                                               ^ (((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                   << 0x34U) 
                                                  | (((QData)((IData)(
                                                                      vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                      << 0x14U) 
                                                     | ((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U])) 
                                                        >> 0xcU))))
                                            : ((1U 
                                                == 
                                                (3U 
                                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                                    >> 8U)))
                                                ? (
                                                   (((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U])) 
                                                     << 0x33U) 
                                                    | (((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U])) 
                                                        << 0x13U) 
                                                       | ((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                          >> 0xdU))) 
                                                   | (((QData)((IData)(
                                                                       vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                       << 0x34U) 
                                                      | (((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                          << 0x14U) 
                                                         | ((QData)((IData)(
                                                                            vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U])) 
                                                            >> 0xcU))))
                                                : (
                                                   (2U 
                                                    == 
                                                    (3U 
                                                     & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                                        >> 8U)))
                                                    ? 
                                                   ((((QData)((IData)(
                                                                      vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U])) 
                                                      << 0x33U) 
                                                     | (((QData)((IData)(
                                                                         vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U])) 
                                                         << 0x13U) 
                                                        | ((QData)((IData)(
                                                                           vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                           >> 0xdU))) 
                                                    & (((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                        << 0x34U) 
                                                       | (((QData)((IData)(
                                                                           vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                           << 0x14U) 
                                                          | ((QData)((IData)(
                                                                             vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U])) 
                                                             >> 0xcU))))
                                                    : 
                                                   (((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U])) 
                                                     << 0x33U) 
                                                    | (((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[4U])) 
                                                        << 0x13U) 
                                                       | ((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                          >> 0xdU)))))) 
                                          << 1U))) 
                              + ((((((0U == (3U & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                                   >> 8U))) 
                                     | (1U == (3U & 
                                               (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                                >> 8U)))) 
                                    | (2U == (3U & 
                                              (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                               >> 8U))))
                                    ? 0ULL : (0x1ffffffffULL 
                                              & ((((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                   << 0x34U) 
                                                  | (((QData)((IData)(
                                                                      vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[3U])) 
                                                      << 0x14U) 
                                                     | ((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U])) 
                                                        >> 0xcU))) 
                                                 ^ 
                                                 (- (QData)((IData)(
                                                                    (1U 
                                                                     & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                                                        >> 2U)))))))) 
                                  << 1U) | (QData)((IData)(
                                                           (1U 
                                                            & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                                               >> 2U)))))) 
                             >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0x7fffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x8000U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                           | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                          >> 0xfU) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                       | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                      >> 0x10U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xbfffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x4000U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                           | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                          >> 0xeU) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                       | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                      >> 0xfU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xdfffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x2000U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                           | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                          >> 0xdU) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                       | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                      >> 0xeU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xefffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x1000U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                           | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                          >> 0xcU) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                       | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                      >> 0xdU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xf7ffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x800U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                          | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                         >> 0xbU) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                      | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                     >> 0xcU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xfbffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x400U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                          | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                         >> 0xaU) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                      | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                     >> 0xbU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xfdffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x200U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                          | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                         >> 9U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                    | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                   >> 0xaU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xfeffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x100U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                          | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                         >> 8U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                    | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                   >> 9U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xff7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x80U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                         | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                        >> 7U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                   | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                  >> 8U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xffbfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x40U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                         | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                        >> 6U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                   | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                  >> 7U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xffdfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x20U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                         | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                        >> 5U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                   | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                  >> 6U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xffefU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x10U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                         | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                        >> 4U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                   | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                                  >> 5U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xfff7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (8U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                      | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                     >> 3U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                               >> 4U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xfffbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (4U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                      | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                     >> 2U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                               >> 3U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xfffdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (2U & (((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                      | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                     >> 1U) & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                                | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                               >> 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0xfffeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (1U & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                     | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                    & ((taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_a 
                        | taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__eq_b) 
                       >> 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a 
        = ((0x7fffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
           | (0x8000U & ((0xffff8000U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
                         ^ (0xf8000U & (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U] 
                                        >> 0xcU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U] 
        = (((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__pc_ex)) 
                      << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc_ex)))) 
            << 4U) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_taken_ex) 
                       << 3U) | ((4U & ((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__jal_jalr_ex)) 
                                        << 2U)) | (
                                                   ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__is_return) 
                                                    << 1U) 
                                                   | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__is_call)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__br_results[1U] 
        = (((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__pc_ex)) 
                      << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc_ex)))) 
            >> 0x1cU) | ((IData)(((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__pc_ex)) 
                                    << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc_ex))) 
                                  >> 0x20U)) << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__br_results[2U] 
        = (((IData)(((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__pc_ex)) 
                       << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc_ex))) 
                     >> 0x20U)) >> 0x1cU) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__id_ex) 
                                              << 5U) 
                                             | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__instruction_is_completing) 
                                                << 4U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_flush 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__instruction_is_completing) 
           & ((0x7fffffffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U] 
                               << 4U) | (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U] 
                                         >> 0x1cU))) 
              != (vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc_ex 
                  >> 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__issue_request 
        = (((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__inflight_count) 
              >> 3U) & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_conflict))) 
            | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_output_valid)) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__ready_for_issue_from_lsq));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected 
        = (IData)((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__inflight_count) 
                    >> 3U) & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_conflict))));
    taiga_sim__DOT__l2_to_mem__DOT__amo_unit__DOT__rs1_smaller_than_rs2 
        = VL_LTS_IQQ(33, (((QData)((IData)(((~ (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                >> 4U)) 
                                            & (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                               >> 4U)))) 
                           << 0x20U) | (QData)((IData)(
                                                       ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                                         << 0x1bU) 
                                                        | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                           >> 5U))))), 
                     (((QData)((IData)((1U & ((~ (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                  >> 4U)) 
                                              & (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                 >> 4U))))) 
                       << 0x20U) | (QData)((IData)(
                                                   ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                     << 0x1bU) 
                                                    | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                       >> 5U))))));
    if (vlSelf->taiga_sim__DOT__l2_to_mem__DOT__read_modify_write) {
        vlSelf->ddr_axi_wstrb = 0xfU;
        vlSelf->ddr_axi_wdata = vlSelf->taiga_sim__DOT__l2_to_mem__DOT__amo_result_r;
        vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_reference_burst_count = 0U;
    } else {
        vlSelf->ddr_axi_wstrb = (0xfU & (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                 >> 0xaU)));
        vlSelf->ddr_axi_wdata = vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out;
        vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_reference_burst_count 
            = (0x1fU & (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                >> 3U)));
    }
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__pop = (
                                                   (((IData)(vlSelf->taiga_sim__DOT__axi_arvalid) 
                                                     & (IData)(vlSelf->ddr_axi_arready)) 
                                                    & (~ (IData)(vlSelf->taiga_sim__DOT__l2_to_mem__DOT__read_modify_write))) 
                                                   | ((IData)(vlSelf->taiga_sim__DOT__axi_awvalid) 
                                                      & (IData)(vlSelf->ddr_axi_awready)));
    vlSelf->taiga_sim__DOT__cpu__DOT__early_branch_flush 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__valid_fetch_result) 
             & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram.data_valid)) 
            & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo.data_out) 
               >> 4U)) & (~ (IData)(taiga_sim__DOT__cpu__DOT__fetch_block__DOT__is_branch_or_jump)));
    vlSelf->taiga_sim__DOT__l2_arb__DOT__arb_request 
        = vlSelf->taiga_sim__DOT__l2_arb__DOT__requests
        [vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.grantee_i];
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.grantee_v = 0U;
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.grantee_v 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.grantee_v) 
           | (3U & ((IData)(1U) << (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.grantee_i))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_ids
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_ids
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_if 
        = ((((0x2dU >= (0x3fU & ((IData)(0x17U) * (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way))))
              ? (3U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry 
                               >> (0x3fU & ((IData)(0x17U) 
                                            * (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way))))))
              : 0U) << 3U) | (((IData)((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches))) 
                               << 2U) | ((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches))
                                          ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches)
                                          : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__replacement_way))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__bp.is_branch 
        = ((0x2dU >= (0x3fU & ((IData)(4U) + ((IData)(0x17U) 
                                              * (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way))))) 
           & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry 
                      >> (0x3fU & ((IData)(4U) + ((IData)(0x17U) 
                                                  * (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way)))))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__bp.is_return 
        = ((0x2dU >= (0x3fU & ((IData)(3U) + ((IData)(0x17U) 
                                              * (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way))))) 
           & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry 
                      >> (0x3fU & ((IData)(3U) + ((IData)(0x17U) 
                                                  * (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way)))))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_shortened.start 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__start_algorithm_r) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__early_terminate)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[0U] 
        = ((0xfffffffeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[0U]) 
           | (1U & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__expo_normalized) 
                    >> 0xbU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[0U] 
        = ((0xfffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[0U]) 
           | ((IData)((((QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U] 
                                               >> 0xfU)))) 
                        << 0x3fU) | (((QData)((IData)(
                                                      (0x7ffU 
                                                       & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__expo_normalized)))) 
                                      << 0x34U) | (0xfffffffffffffULL 
                                                   & (((QData)((IData)(
                                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U])) 
                                                       << 0x30U) 
                                                      | (((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[4U])) 
                                                          << 0x10U) 
                                                         | ((QData)((IData)(
                                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[3U])) 
                                                            >> 0x10U))))))) 
              << 0x14U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[1U] 
        = (((IData)((((QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U] 
                                             >> 0xfU)))) 
                      << 0x3fU) | (((QData)((IData)(
                                                    (0x7ffU 
                                                     & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__expo_normalized)))) 
                                    << 0x34U) | (0xfffffffffffffULL 
                                                 & (((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U])) 
                                                     << 0x30U) 
                                                    | (((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[4U])) 
                                                        << 0x10U) 
                                                       | ((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[3U])) 
                                                          >> 0x10U))))))) 
            >> 0xcU) | ((IData)(((((QData)((IData)(
                                                   (1U 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U] 
                                                       >> 0xfU)))) 
                                   << 0x3fU) | (((QData)((IData)(
                                                                 (0x7ffU 
                                                                  & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__expo_normalized)))) 
                                                 << 0x34U) 
                                                | (0xfffffffffffffULL 
                                                   & (((QData)((IData)(
                                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U])) 
                                                       << 0x30U) 
                                                      | (((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[4U])) 
                                                          << 0x10U) 
                                                         | ((QData)((IData)(
                                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[3U])) 
                                                            >> 0x10U)))))) 
                                 >> 0x20U)) << 0x14U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs[2U] 
        = ((IData)(((((QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U] 
                                             >> 0xfU)))) 
                      << 0x3fU) | (((QData)((IData)(
                                                    (0x7ffU 
                                                     & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__expo_normalized)))) 
                                    << 0x34U) | (0xfffffffffffffULL 
                                                 & (((QData)((IData)(
                                                                     vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[5U])) 
                                                     << 0x30U) 
                                                    | (((QData)((IData)(
                                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[4U])) 
                                                        << 0x10U) 
                                                       | ((QData)((IData)(
                                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed[3U])) 
                                                          >> 0x10U)))))) 
                    >> 0x20U)) >> 0xcU);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz 
        = ((0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)) 
           | (0x80U & ((~ (IData)((0U != (0xfU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                                                  >> 0xbU))))) 
                       << 7U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[7U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                >> 0xcU))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz 
        = ((0xbfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)) 
           | (0x40U & ((~ (IData)((0U != (0xfU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                                                  >> 0xfU))))) 
                       << 6U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[6U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                >> 0x10U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz 
        = ((0xdfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)) 
           | (0x20U & ((~ (IData)((0U != (0xfU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                                                  >> 0x13U))))) 
                       << 5U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[5U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                >> 0x14U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz 
        = ((0xefU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)) 
           | (0x10U & ((~ (IData)((0U != (0xfU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                                                  >> 0x17U))))) 
                       << 4U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[4U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                >> 0x18U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz 
        = ((0xf7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)) 
           | (8U & ((~ (IData)((0U != (0xfU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                                               >> 0x1bU))))) 
                    << 3U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                >> 0x1cU))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz 
        = ((0xfbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)) 
           | (4U & ((~ (IData)((0U != (0xfU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[5U] 
                                                << 1U) 
                                               | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[4U] 
                                                  >> 0x1fU)))))) 
                    << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table
        [(7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[5U])];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz 
        = ((0xfdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)) 
           | (2U & ((~ (IData)((0U != (0xfU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[5U] 
                                               >> 3U))))) 
                    << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[5U] 
                >> 4U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz 
        = ((0xfeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)) 
           | (1U & (~ (IData)((0U != (0xfU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[5U] 
                                              >> 7U)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed[5U] 
                >> 8U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz 
        = ((0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz)) 
           | ((IData)((0xfU == (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)))) 
              << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz 
        = ((0x17U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz)) 
           | (((0x10U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz))
                ? (3U == (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz) 
                                >> 4U))) : (3U == (3U 
                                                   & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)))) 
              << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz 
        = ((0x1bU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz)) 
           | (4U & (((((IData)((1U == (3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)))) 
                       | (IData)((7U == (0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz))))) 
                      | (IData)((0x1fU == (0x3fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz))))) 
                     | (0x7fU == (0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz)))) 
                    << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__upper_lower[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz
        [(1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__upper_lower[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz
        [(2U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz) 
                      >> 2U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__upper_lower[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz
        [(4U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz) 
                      >> 4U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__upper_lower[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz
        [(6U | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz) 
                      >> 6U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz 
        = ((0x1cU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz)) 
           | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__upper_lower
           [(3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz) 
                   >> 3U))]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[8U] 
        = ((0x7ffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[8U]) 
           | (0x80000U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done
                           [1U] << 0x13U) & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__instruction
                                             [2U] << 0x11U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[0U] 
        = ((0xfffe1fffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[0U]) 
           | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case
              [2U] << 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[0U] 
        = ((0x1fffffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[0U]) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3
                      [2U]) << 0x1dU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[1U] 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3
                    [2U]) >> 3U) | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3
                                             [2U] >> 0x20U)) 
                                    << 0x1dU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[2U] 
        = (((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3
                     [2U] >> 0x20U)) >> 3U) | (((IData)((QData)((IData)(
                                                                        (1U 
                                                                         & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode
                                                                            [2U] 
                                                                            >> 3U))))) 
                                                << 0x1eU) 
                                               | (0x20000000U 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode
                                                     [2U] 
                                                     << 0x1bU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[3U] 
        = ((0x1fffffffU & ((IData)((QData)((IData)(
                                                   (1U 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode
                                                       [2U] 
                                                       >> 3U))))) 
                           >> 2U)) | ((0x20000000U 
                                       & ((IData)((QData)((IData)(
                                                                  (1U 
                                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode
                                                                      [2U] 
                                                                      >> 3U))))) 
                                          >> 2U)) | 
                                      ((IData)(((QData)((IData)(
                                                                (1U 
                                                                 & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode
                                                                    [2U] 
                                                                    >> 3U)))) 
                                                >> 0x20U)) 
                                       << 0x1eU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[4U] 
        = (((0x1ff80000U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                    [0U]) << 0x13U)) 
            | (0x1fffffffU & ((IData)(((QData)((IData)(
                                                       (1U 
                                                        & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode
                                                           [2U] 
                                                           >> 3U)))) 
                                       >> 0x20U)) >> 2U))) 
           | ((0x20000000U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                       [0U]) << 0x13U) 
                              | ((IData)(((QData)((IData)(
                                                          (1U 
                                                           & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode
                                                              [2U] 
                                                              >> 3U)))) 
                                          >> 0x20U)) 
                                 >> 2U))) | (0xc0000000U 
                                             & ((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                                        [0U]) 
                                                << 0x13U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[5U] 
        = ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                     [0U]) >> 0xdU) | (0x1ff80000U 
                                       & ((IData)((
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                                   [0U] 
                                                   >> 0x20U)) 
                                          << 0x13U))) 
           | ((0x20000000U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                       [0U] >> 0x20U)) 
                              << 0x13U)) | (0xc0000000U 
                                            & ((IData)(
                                                       (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                                        [0U] 
                                                        >> 0x20U)) 
                                               << 0x13U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[6U] 
        = ((0xffffff80U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[6U]) 
           | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                       [0U] >> 0x20U)) >> 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm[0U] 
        = ((0xfc7U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm
            [0U]) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm
                     [3U] << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign[0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_sign
           [2U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_sign
           [2U]);
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo_intermediate 
        = (0x1fffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_expo
                       [2U] + (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_expo
                               [2U] - vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt
                               [2U])) - (IData)(0x3ffU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_fflags[0U][1U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation
           [3U] << 4U);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN[0U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation
            [0U] | (0U != (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                                 >> 3U)))) | (0U != 
                                              (3U & 
                                               ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                                                 << 1U) 
                                                | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
                                                   >> 0x1fU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[1U][0U] 
        = ((0x400U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out))
            ? ((0x200U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out))
                ? taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data
                : ((0x100U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out))
                    ? (0xffffU & taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data)
                    : (0xffU & taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data)))
            : ((0x200U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out))
                ? taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data
                : ((0x100U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.data_out))
                    ? VL_EXTENDS_II(32,16, (0xffffU 
                                            & taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data))
                    : VL_EXTENDS_II(32,8, (0xffU & taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__aligned_load_data)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__unit_fflag_wb_packet 
        = ((0x1e0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__unit_fflag_wb_packet)) 
           | ((5U >= vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
               [1U]) ? vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags
              [1U][vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
              [1U]] : 0U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet[0U] 
        = ((0x1ffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
            [0U]) | ((QData)((IData)(((0x11U >= (0x1fU 
                                                 & ((IData)(3U) 
                                                    * 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                                    [0U])))
                                       ? (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id
                                                [0U] 
                                                >> 
                                                (0x1fU 
                                                 & ((IData)(3U) 
                                                    * 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                                    [0U]))))
                                       : 0U))) << 0x21U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet[1U] 
        = ((0x1ffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
            [1U]) | ((QData)((IData)(((0x11U >= (0x1fU 
                                                 & ((IData)(3U) 
                                                    * 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                                    [1U])))
                                       ? (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id
                                                [1U] 
                                                >> 
                                                (0x1fU 
                                                 & ((IData)(3U) 
                                                    * 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                                    [1U]))))
                                       : 0U))) << 0x21U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed 
        = ((0x7bfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed)) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_ifence) 
              << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed 
        = ((0x7fdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed)) 
           | (((((((0U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                    >> 0xeU))) | (8U 
                                                  == 
                                                  (0x1fU 
                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                                      >> 0xeU)))) 
                  | (0xbU == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                       >> 0xeU)))) 
                 | (1U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                    >> 0xeU)))) | (9U 
                                                   == 
                                                   (0x1fU 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                                       >> 0xeU)))) 
               | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fence)) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed 
        = ((3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed)) 
           | (((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_f2i) 
                 | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fcmp)) 
                | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_class)) 
               << 3U) | ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_i2f) 
                           | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_minmax)) 
                          | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_sign_inj)) 
                         << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed 
        = ((0x7fbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed)) 
           | ((IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_csr) 
              << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__uses_rd 
        = (1U & (((((((((0xdU == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                           >> 0xeU))) 
                        | (5U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                           >> 0xeU)))) 
                       | (0x1bU == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                             >> 0xeU)))) 
                      | (0x19U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                            >> 0xeU)))) 
                     | (0U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                        >> 0xeU)))) 
                    | (4U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                       >> 0xeU)))) 
                   | (0xcU == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                        >> 0xeU)))) 
                  | (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_csr)) 
                 | vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed 
        = ((0x7feU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed)) 
           | (((((((0xcU == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                      >> 0xeU))) | 
                   (4U == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                    >> 0xeU)))) | (5U 
                                                   == 
                                                   (0x1fU 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                                       >> 0xeU)))) 
                 | (0xdU == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                      >> 0xeU)))) | 
                (0x1bU == (0x1fU & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                    >> 0xeU)))) | (0x19U 
                                                   == 
                                                   (0x1fU 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                                       >> 0xeU)))) 
              & (~ (IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__mult_div_op))));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed 
        = ((0x7f7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed)) 
           | (((IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__mult_div_op) 
               & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                     >> 0x1aU))) << 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed 
        = ((0x7efU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed)) 
           | (0x3f0U & (((IData)(taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__mult_div_op) 
                         << 4U) & (vlSelf->taiga_sim__DOT__cpu__DOT__decode[0U] 
                                   >> 0x16U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[0U] 
        = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.phys_rd_addr;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr[1U] 
        = (0x1fU & (IData)(TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface__DOT__rs_addr));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr[2U] 
        = (0x1fU & ((IData)(TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface__DOT__rs_addr) 
                    >> 5U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr[3U] 
        = (0x1fU & ((IData)(TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface__DOT__rs_addr) 
                    >> 0xaU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__flt 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__sign_equ)
                  ? (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                       >> 0x17U) ^ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                    >> 0x16U)) & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__feq)))
                  : ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                      >> 0x16U) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[2U] 
                                      >> 0x13U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int 
        = ((0x400U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[7U])
            ? 0U : ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac[2U] 
                     << 0xcU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac[1U] 
                                 >> 0x14U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR 
        = ((0x3cU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR)) 
           | (((IData)((0U != (0x3fU & (IData)(((QData)((IData)(
                                                                (0x7fffffffU 
                                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int))) 
                                                >> 6U))))) 
               << 1U) | (0U != (0x3fU & (IData)((QData)((IData)(
                                                                (0x7fffffffU 
                                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR 
        = ((0x33U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR)) 
           | ((((IData)((0U != (0x3fU & (IData)(((QData)((IData)(
                                                                 (0x7fffffffU 
                                                                  & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int))) 
                                                 >> 0x12U))))) 
                << 1U) | (0U != (0x3fU & (IData)(((QData)((IData)(
                                                                  (0x7fffffffU 
                                                                   & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int))) 
                                                  >> 0xcU))))) 
              << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR 
        = ((0xfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR)) 
           | ((((IData)((0U != (0x3fU & (IData)(((QData)((IData)(
                                                                 (0x7fffffffU 
                                                                  & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int))) 
                                                 >> 0x1eU))))) 
                << 1U) | (0U != (0x3fU & (IData)(((QData)((IData)(
                                                                  (0x7fffffffU 
                                                                   & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int))) 
                                                  >> 0x18U))))) 
              << 4U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
        = (0x1fffffffffffffULL & ((0x400U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[7U])
                                   ? (((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[8U])) 
                                       << 0x35U) | 
                                      (((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[8U])) 
                                        << 0x15U) | 
                                       ((QData)((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[7U])) 
                                        >> 0xbU))) : 
                                  (0x1ffffffffffffeULL 
                                   & (((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac[1U])) 
                                       << 0x21U) | 
                                      ((QData)((IData)(
                                                       vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac[0U])) 
                                       << 1U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR 
        = ((0x1fcU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR)) 
           | (((IData)((0U != (0x3fU & (IData)((0x1fffffffffffULL 
                                                & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                                   >> 6U)))))) 
               << 1U) | (0U != (0x3fU & (IData)((0x7ffffffffffffULL 
                                                 & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR 
        = ((0x1f3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR)) 
           | ((((IData)((0U != (0x3fU & (IData)((0x1ffffffffULL 
                                                 & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                                    >> 0x12U)))))) 
                << 1U) | (0U != (0x3fU & (IData)((0x7fffffffffULL 
                                                  & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                                     >> 0xcU)))))) 
              << 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR 
        = ((0x1cfU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR)) 
           | ((((IData)((0U != (0x3fU & (IData)((0x1fffffULL 
                                                 & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                                    >> 0x1eU)))))) 
                << 1U) | (0U != (0x3fU & (IData)((0x7ffffffULL 
                                                  & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                                     >> 0x18U)))))) 
              << 4U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR 
        = ((0x13fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR)) 
           | ((((IData)((0U != (0x3fU & (IData)((0x1ffULL 
                                                 & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                                    >> 0x2aU)))))) 
                << 1U) | (0U != (0x3fU & (IData)((0x7fffULL 
                                                  & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                                     >> 0x24U)))))) 
              << 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR 
        = ((0xffU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR)) 
           | ((IData)((0U != (0x3fU & (IData)((7ULL 
                                               & (taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                                  >> 0x30U)))))) 
              << 8U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__grs 
        = ((0x400U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[7U])
            ? ((1U == (0x7ffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[7U] 
                                  << 1U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                            >> 0x1fU))))
                ? ((6U & ((IData)((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                   >> 0x33U)) << 1U)) 
                   | (0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR)))
                : ((2U == (0x7ffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[7U] 
                                      << 1U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                                >> 0x1fU))))
                    ? ((2U & ((IData)((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                       >> 0x34U)) << 1U)) 
                       | (1U & ((IData)((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                         >> 0x33U)) 
                                | (0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR)))))
                    : ((0U != (3U & (IData)((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                                             >> 0x33U)))) 
                       | (0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR)))))
            : ((6U & ((IData)((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac 
                               >> 0x33U)) << 1U)) | 
               (0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR))));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__data_attributes.push 
        = (((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_valid) 
            & (~ (IData)((vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request 
                          >> 8U)))) & (~ (IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT____Vcellout__reserv__abort)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__normalized_radicand 
        = (0xffffffffffffffULL & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt.radicand 
                                  << (0x3fU & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__radicand_clz) 
                                               - (1U 
                                                  & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__radicand_clz))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__terminate 
        = (VL_LTS_III(32, 0x38U, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__counter) 
           | (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__early_terminate));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt[0U] 
        = ((0xffe003fffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt
            [0U]) | ((QData)((IData)((0x7ffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                                                [0U]
                                                 ? 
                                                ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo) 
                                                 + (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__right_shift))
                                                 : (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb.right_shift_amt))))) 
                     << 0x16U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow[0U] 
        = ((0xbU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow
            [0U]) | (4U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done
                            [0U] ? (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo) 
                                     >> 0xbU) & (~ 
                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case
                                                 [0U]))
                             : (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt_wb.expo_overflow)) 
                           << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm[0U] 
        = ((0xff8U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm
            [0U]) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm
           [2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__zero_result_sign[0U] 
        = ((2U == vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm
            [0U]) ? 1U : 0U);
    __Vtemp_h8f86743b__0[0U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
        [0U][0U];
    __Vtemp_h8f86743b__0[1U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
        [0U][1U];
    __Vtemp_h8f86743b__0[2U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
        [0U][2U];
    __Vtemp_h8f86743b__0[3U] = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac
                                         [0U]) << 8U) 
                                | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                [0U][3U]);
    __Vtemp_h8f86743b__0[4U] = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac
                                         [0U]) >> 0x18U) 
                                | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac
                                            [0U] >> 0x20U)) 
                                   << 8U));
    VL_SHIFTR_WWI(158,158,12, __Vtemp_hb4d0d369__0, __Vtemp_h8f86743b__0, 
                  vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff
                  [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_in[0U] 
        = __Vtemp_hb4d0d369__0[0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_in[1U] 
        = __Vtemp_hb4d0d369__0[1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_in[2U] 
        = __Vtemp_hb4d0d369__0[2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_in[3U] 
        = (0xffU & __Vtemp_hb4d0d369__0[3U]);
    __Vtemp_hf39bef00__0[0U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
        [0U][0U];
    __Vtemp_hf39bef00__0[1U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
        [0U][1U];
    __Vtemp_hf39bef00__0[2U] = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
        [0U][2U];
    __Vtemp_hf39bef00__0[3U] = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac
                                         [0U]) << 8U) 
                                | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                [0U][3U]);
    __Vtemp_hf39bef00__0[4U] = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac
                                         [0U]) >> 0x18U) 
                                | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac
                                            [0U] >> 0x20U)) 
                                   << 8U));
    VL_SHIFTR_WWI(158,158,12, __Vtemp_hb50f37c1__0, __Vtemp_hf39bef00__0, 
                  vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff
                  [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned[0U] 
        = (0x3fffffffffffffULL & (((QData)((IData)(
                                                   (0x3fffffffU 
                                                    & __Vtemp_hb50f37c1__0[4U]))) 
                                   << 0x18U) | ((QData)((IData)(
                                                                __Vtemp_hb50f37c1__0[3U])) 
                                                >> 8U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation[0U] 
        = (1U & ((0U != (0x11000000U & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U])) 
                 | (((~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[8U] 
                         >> 0x13U)) & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r[0U] 
                                       >> 0x15U)) | 
                    ((IData)((0x22000000U == (0x22000000U 
                                              & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U]))) 
                     & ((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[8U] 
                         >> 0xcU) ^ (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs2_sign))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract[0U] 
        = (IData)(((taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[8U] 
                    >> 0xcU) ^ (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__temp_rs2_sign)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_rd[0U][1U] 
        = ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__overflowExp)
            ? (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[1U])) 
                << 0x20U) | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[0U])))
            : (((QData)((IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[4U] 
                                       >> 8U)))) << 0x3fU) 
               | (((QData)((IData)((0x7ffU & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[4U] 
                                                << 3U) 
                                               | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[3U] 
                                                  >> 0x1dU)) 
                                              + (0x1ffU 
                                                 == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs)))))) 
                   << 0x34U) | taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_out)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__underflowExp 
        = ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
               >> 7U)) & (0U != taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_out));
    __Vtemp_h30e72d2b__0[0U] = ((((IData)((((QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend)) 
                                            << 0x20U) 
                                           | (QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor)))) 
                                  << 0x12U) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ) 
                                                << 0xdU) 
                                               | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ) 
                                                   << 8U) 
                                                  | (0x80U 
                                                     & (taiga_sim__DOT__cpu__DOT__div_inputs[0U] 
                                                        << 5U))))) 
                                | ((((~ (taiga_sim__DOT__cpu__DOT__div_inputs[0U] 
                                         >> 1U)) & 
                                     (taiga_sim__DOT__cpu__DOT__div_inputs[2U] 
                                      >> 2U)) << 6U) 
                                   | ((0x20U & (((~ 
                                                  (taiga_sim__DOT__cpu__DOT__div_inputs[0U] 
                                                   >> 1U)) 
                                                 << 5U) 
                                                & ((taiga_sim__DOT__cpu__DOT__div_inputs[2U] 
                                                    ^ 
                                                    taiga_sim__DOT__cpu__DOT__div_inputs[1U]) 
                                                   << 3U))) 
                                      | ((((0x1fU == (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ)) 
                                           & (~ (taiga_sim__DOT__cpu__DOT__div_inputs[0U] 
                                                 >> 3U))) 
                                          << 4U) | 
                                         ((8U & (taiga_sim__DOT__cpu__DOT__div_inputs[0U] 
                                                 << 3U)) 
                                          | (7U & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                                   >> 0xfU)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__fifo_inputs[0U] 
        = __Vtemp_h30e72d2b__0[0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__fifo_inputs[1U] 
        = ((0x7fU & (((IData)((((QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend)) 
                                << 0x20U) | (QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor)))) 
                      >> 0xeU) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ) 
                                   >> 0x13U) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ) 
                                                >> 0x18U)))) 
           | ((0x3ff80U & ((IData)((((QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend)) 
                                     << 0x20U) | (QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor)))) 
                           >> 0xeU)) | ((IData)(((((QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend)) 
                                                   << 0x20U) 
                                                  | (QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor))) 
                                                 >> 0x20U)) 
                                        << 0x12U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__fifo_inputs[2U] 
        = ((0x7fU & ((IData)(((((QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend)) 
                                << 0x20U) | (QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor))) 
                              >> 0x20U)) >> 0xeU)) 
           | (0x3ff80U & ((IData)(((((QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_dividend)) 
                                     << 0x20U) | (QData)((IData)(taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__unsigned_divisor))) 
                                   >> 0x20U)) >> 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[0U][0U] 
        = ((0U == (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                         >> 0xaU))) ? ((vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[1U] 
                                        << 0x14U) | 
                                       (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                        >> 0xcU)) : 
           ((1U == (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                          >> 0xaU))) ? (IData)(taiga_sim__DOT__cpu__DOT__alu_unit_block__DOT__add_sub_result)
             : ((2U == (3U & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                              >> 0xaU))) ? (1U & (IData)(
                                                         (taiga_sim__DOT__cpu__DOT__alu_unit_block__DOT__add_sub_result 
                                                          >> 0x20U)))
                 : (IData)((0x7fffffffffffffffULL & 
                            (((1U & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U])
                               ? ((QData)((IData)((
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U] 
                                                    << 0x14U) 
                                                   | (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[1U] 
                                                      >> 0xcU)))) 
                                  << 0x1fU) : (((QData)((IData)(
                                                                (0x7fffffffU 
                                                                 & (- (IData)(
                                                                              (1U 
                                                                               & (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                                                                >> 1U))))))) 
                                                << 0x20U) 
                                               | (QData)((IData)(
                                                                 ((vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[2U] 
                                                                   << 0x14U) 
                                                                  | (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[1U] 
                                                                     >> 0xcU)))))) 
                             >> (0x1fU & (((vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                            << 0x1dU) 
                                           | (vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U] 
                                              >> 3U)) 
                                          ^ (- (IData)(
                                                       (1U 
                                                        & vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs[0U])))))))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_taken 
        = (1U & ((1U & ((((((0x20000000U & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U])
                             ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a)
                             : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a)) 
                           << 1U) | (IData)(taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__carry_in)) 
                         + ((((0x20000000U & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U])
                               ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b)
                               : 0U) << 1U) | (IData)(taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__carry_in))) 
                        >> 0x10U)) | (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U] 
                                      >> 0x17U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry 
        = ((0x7fffe3U & vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry) 
           | (0x1cU & (vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U] 
                       << 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_mux[1U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__br_results[1U] 
            << 0x1cU) | (vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U] 
                         >> 4U));
    __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__5__pc 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__br_results[2U] 
            << 0x1cU) | (vlSelf->taiga_sim__DOT__cpu__DOT__br_results[1U] 
                         >> 4U));
    __Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__5__Vfuncout 
        = (0x1ffffU & (__Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__5__pc 
                       >> 0xbU));
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry 
        = ((0x40001fU & vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry) 
           | (__Vfunc_taiga_sim__DOT__cpu__DOT__bp_block__DOT__get_tag__5__Vfuncout 
              << 5U));
    taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex 
        = vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__br_results[2U] 
                >> 5U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] = ((0x7bfffU 
                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U]) 
                                                | (0x7ffffU 
                                                   & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_flush) 
                                                       | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc_override)) 
                                                      << 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_ack 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__issue_request) 
           & (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_ack 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__issue_request) 
           & (~ (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)));
    __Vtemp_hef1d8ee0__0[1U] = (((IData)(((((QData)((IData)(
                                                            ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                              ? (IData)(
                                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                                         >> 0xcU))
                                                              : (IData)(
                                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                         >> 0xbU))))) 
                                            << 6U) 
                                           | ((QData)((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)) 
                                              << 5U)) 
                                          | (QData)((IData)(
                                                            ((0x10U 
                                                              & ((~ (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)) 
                                                                 << 4U)) 
                                                             | ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                                 ? 0U
                                                                 : 
                                                                (0xfU 
                                                                 & (IData)(
                                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                            >> 7U))))))))) 
                                 << 3U) | (IData)((
                                                   (((QData)((IData)(
                                                                     (7U 
                                                                      & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                                          ? (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                                                >> 9U))
                                                                          : (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                                >> 4U)))))) 
                                                     << 0x20U) 
                                                    | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data))) 
                                                   >> 0x20U)));
    __Vtemp_hef1d8ee0__0[2U] = (((IData)(((((QData)((IData)(
                                                            ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                              ? (IData)(
                                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                                         >> 0xcU))
                                                              : (IData)(
                                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                         >> 0xbU))))) 
                                            << 6U) 
                                           | ((QData)((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)) 
                                              << 5U)) 
                                          | (QData)((IData)(
                                                            ((0x10U 
                                                              & ((~ (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)) 
                                                                 << 4U)) 
                                                             | ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                                 ? 0U
                                                                 : 
                                                                (0xfU 
                                                                 & (IData)(
                                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                            >> 7U))))))))) 
                                 >> 0x1dU) | ((IData)(
                                                      (((((QData)((IData)(
                                                                          ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                                            ? (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                                                >> 0xcU))
                                                                            : (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                                >> 0xbU))))) 
                                                          << 6U) 
                                                         | ((QData)((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)) 
                                                            << 5U)) 
                                                        | (QData)((IData)(
                                                                          ((0x10U 
                                                                            & ((~ (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)) 
                                                                               << 4U)) 
                                                                           | ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                                               ? 0U
                                                                               : 
                                                                              (0xfU 
                                                                               & (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                                >> 7U)))))))) 
                                                       >> 0x20U)) 
                                              << 3U));
    __Vtemp_hfa356fe8__0[2U] = ((((IData)((((QData)((IData)(
                                                            (7U 
                                                             & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                                 ? (IData)(
                                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                                            >> 9U))
                                                                 : (IData)(
                                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                            >> 4U)))))) 
                                            << 0x20U) 
                                           | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data)))) 
                                  << 5U) | ((0x1cU 
                                             & ((IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                         >> 6U)) 
                                                << 2U)) 
                                            | (2U & 
                                               (((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                  ? (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                             >> 1U))
                                                  : (IData)(
                                                            (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                             >> 2U))) 
                                                << 1U)))) 
                                | ((IData)((((1U & (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr))
                                              ? vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb
                                             [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest]
                                              : vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_issue
                                             [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest]) 
                                            >> 0x20U)) 
                                   >> 0x1fU));
    __Vtemp_hfa356fe8__0[3U] = ((1U & ((IData)((((QData)((IData)(
                                                                 (7U 
                                                                  & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                                      ? (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                                                >> 9U))
                                                                      : (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                                >> 4U)))))) 
                                                 << 0x20U) 
                                                | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data)))) 
                                       >> 0x1bU)) | 
                                ((0x1eU & ((IData)(
                                                   (((QData)((IData)(
                                                                     (7U 
                                                                      & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                                                                          ? (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out 
                                                                                >> 9U))
                                                                          : (IData)(
                                                                                (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                                                                >> 4U)))))) 
                                                     << 0x20U) 
                                                    | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data)))) 
                                           >> 0x1bU)) 
                                 | (__Vtemp_hef1d8ee0__0[1U] 
                                    << 5U)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[0U] 
        = (((IData)(((1U & (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr))
                      ? vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb
                     [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest]
                      : vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_issue
                     [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest])) 
            << 1U) | (1U & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_selected)
                             ? (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out)
                             : (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry 
                                        >> 1U)))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[1U] 
        = (((IData)(((1U & (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr))
                      ? vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb
                     [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest]
                      : vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_issue
                     [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest])) 
            >> 0x1fU) | ((IData)((((1U & (IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__output_attr))
                                    ? vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb
                                   [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest]
                                    : vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_issue
                                   [vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest]) 
                                  >> 0x20U)) << 1U));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[2U] 
        = __Vtemp_hfa356fe8__0[2U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
        = __Vtemp_hfa356fe8__0[3U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[4U] 
        = ((1U & (__Vtemp_hef1d8ee0__0[1U] >> 0x1bU)) 
           | ((0x1eU & (__Vtemp_hef1d8ee0__0[1U] >> 0x1bU)) 
              | (__Vtemp_hef1d8ee0__0[2U] << 5U)));
    if (((((((((1U == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U])) 
               | (0U == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))) 
              | (4U == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))) 
             | (0xcU == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))) 
            | (8U == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))) 
           | (0x10U == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))) 
          | (0x14U == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))) 
         | (0x18U == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U])))) {
        vlSelf->taiga_sim__DOT__l2_to_mem__DOT__amo_result 
            = ((1U == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))
                ? ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                    << 0x1bU) | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                 >> 5U)) : ((0U == 
                                             (0x1fU 
                                              & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))
                                             ? (((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                                  << 0x1bU) 
                                                 | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                    >> 5U)) 
                                                + (
                                                   (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                    << 0x1bU) 
                                                   | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                      >> 5U)))
                                             : ((4U 
                                                 == 
                                                 (0x1fU 
                                                  & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))
                                                 ? 
                                                (((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                                   << 0x1bU) 
                                                  | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                     >> 5U)) 
                                                 ^ 
                                                 ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                   << 0x1bU) 
                                                  | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                     >> 5U)))
                                                 : 
                                                ((0xcU 
                                                  == 
                                                  (0x1fU 
                                                   & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))
                                                  ? 
                                                 (((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                                    << 0x1bU) 
                                                   | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                      >> 5U)) 
                                                  & ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                      << 0x1bU) 
                                                     | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                        >> 5U)))
                                                  : 
                                                 ((8U 
                                                   == 
                                                   (0x1fU 
                                                    & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))
                                                   ? 
                                                  (((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                                     << 0x1bU) 
                                                    | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                       >> 5U)) 
                                                   | ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                       << 0x1bU) 
                                                      | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                         >> 5U)))
                                                   : 
                                                  ((0x10U 
                                                    == 
                                                    (0x1fU 
                                                     & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))
                                                    ? 
                                                   ((IData)(taiga_sim__DOT__l2_to_mem__DOT__amo_unit__DOT__rs1_smaller_than_rs2)
                                                     ? 
                                                    ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                                      << 0x1bU) 
                                                     | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                        >> 5U))
                                                     : 
                                                    ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                      << 0x1bU) 
                                                     | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                        >> 5U)))
                                                    : 
                                                   ((0x14U 
                                                     == 
                                                     (0x1fU 
                                                      & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))
                                                     ? 
                                                    ((IData)(taiga_sim__DOT__l2_to_mem__DOT__amo_unit__DOT__rs1_smaller_than_rs2)
                                                      ? 
                                                     ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                       << 0x1bU) 
                                                      | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                         >> 5U))
                                                      : 
                                                     ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                                       << 0x1bU) 
                                                      | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                         >> 5U)))
                                                     : 
                                                    ((IData)(taiga_sim__DOT__l2_to_mem__DOT__amo_unit__DOT__rs1_smaller_than_rs2)
                                                      ? 
                                                     ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                                       << 0x1bU) 
                                                      | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                         >> 5U))
                                                      : 
                                                     ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                                       << 0x1bU) 
                                                      | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                                         >> 5U))))))))));
    } else if ((0x1cU == (0x1fU & taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U]))) {
        vlSelf->taiga_sim__DOT__l2_to_mem__DOT__amo_result 
            = ((IData)(taiga_sim__DOT__l2_to_mem__DOT__amo_unit__DOT__rs1_smaller_than_rs2)
                ? ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                    << 0x1bU) | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[0U] 
                                 >> 5U)) : ((taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[2U] 
                                             << 0x1bU) 
                                            | (taiga_sim__DOT__l2_to_mem__DOT__amo_alu_inputs[1U] 
                                               >> 5U)));
    }
    vlSelf->ddr_axi_awlen = vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_reference_burst_count;
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__0__KET__.pop 
        = (IData)(((((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__inflight_count) 
                     >> 4U) & (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.grantee_v)) 
                   & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_addr_fifo.full))));
    vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__input_fifos__BRA__1__KET__.pop 
        = (IData)(((((IData)(vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__inflight_count) 
                     >> 4U) & ((IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__arb.grantee_v) 
                               >> 1U)) & (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__l2_arb__DOT__mem_addr_fifo.full))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_next 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_next)) 
           | ((((IData)((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches))) 
                << 3U) << 1U) | ((((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches)) 
                                   & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__bp.is_branch)) 
                                  << 3U) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__sub_unit_address_match) 
                                             << 2U) 
                                            | ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__itlb.is_fault) 
                                               << 1U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_mux[2U] 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__bp.is_return)
            ? vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram
           [vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index]
            : (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__predicted_pc 
                       >> (0x3fU & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way) 
                                    << 5U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__right_shift[0U] 
        = (1U & (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo_intermediate) 
                  >> 0xcU) | (~ (IData)((0U != (0xfffU 
                                                & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo_intermediate)))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf[0U] 
        = (1U & ((((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                    >> 5U) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
                                 >> 0x1eU))) | (IData)(
                                                       (2U 
                                                        == 
                                                        (6U 
                                                         & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U])))) 
                 & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN
                    [0U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero[0U] 
        = (1U & ((((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U] 
                    >> 2U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[8U] 
                              >> 0x1eU)) | (IData)(
                                                   (0xc00U 
                                                    == 
                                                    (0xc00U 
                                                     & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed[9U])))) 
                 & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN
                    [0U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed 
        = ((0x7fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed)) 
           | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed) 
              << 7U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_fflags[0U][0U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation
            [2U] << 4U) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact
           [2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN[0U] 
        = ((IData)((0U != (0x19800000U & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U]))) 
           | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation
           [0U]);
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1[0U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs
            [1U][0U] << 1U) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
           [1U]);
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1[1U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs
            [1U][0U] >> 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs
                                  [1U][1U] << 1U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1[2U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs
            [1U][1U] >> 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs
                                  [1U][2U] << 1U));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1[3U] 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac
                    [1U]) << 9U) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs
                                     [1U][2U] >> 0x1fU) 
                                    | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs
                                       [1U][3U] << 1U)));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1[4U] 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac
                    [1U]) >> 0x17U) | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac
                                                [1U] 
                                                >> 0x20U)) 
                                       << 9U));
    __Vtemp_h4472ca76__0[1U] = (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                  [1U][0U] ^ (- (IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                        [1U]))) 
                                 >> 0x1fU) | (((2U 
                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                                   [1U][1U] 
                                                   << 1U)) 
                                               | (0xfffffffcU 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                                     [1U][1U] 
                                                     << 1U))) 
                                              ^ ((- (IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                            [1U])) 
                                                 << 1U)));
    __Vtemp_h4472ca76__0[2U] = (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                  [1U][1U] ^ (- (IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                        [1U]))) 
                                 >> 0x1fU) | (((2U 
                                                & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                                   [1U][2U] 
                                                   << 1U)) 
                                               | (0xfffffffcU 
                                                  & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                                     [1U][2U] 
                                                     << 1U))) 
                                              ^ ((- (IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                            [1U])) 
                                                 << 1U)));
    __Vtemp_h4472ca76__0[3U] = (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                  [1U][2U] ^ (- (IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                        [1U]))) 
                                 >> 0x1fU) | ((((IData)(
                                                        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned
                                                        [1U]) 
                                                << 9U) 
                                               | ((2U 
                                                   & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                                      [1U][3U] 
                                                      << 1U)) 
                                                  | (0x1fcU 
                                                     & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                                        [1U][3U] 
                                                        << 1U)))) 
                                              ^ ((- (IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                            [1U])) 
                                                 << 1U)));
    __Vtemp_h4472ca76__0[4U] = (((1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned
                                                [1U]) 
                                        >> 0x17U)) 
                                 ^ ((- (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                               [1U])) 
                                    >> 0x1fU)) | (0xfffffffeU 
                                                  & (((0x1feU 
                                                       & ((IData)(
                                                                  vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned
                                                                  [1U]) 
                                                          >> 0x17U)) 
                                                      | ((IData)(
                                                                 (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned
                                                                  [1U] 
                                                                  >> 0x20U)) 
                                                         << 9U)) 
                                                     ^ 
                                                     ((- (IData)(
                                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                                 [1U])) 
                                                      << 1U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2[0U] 
        = ((((0xfffffffcU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                             [1U][0U] << 1U)) | (2U 
                                                 & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs
                                                     [1U][0U] 
                                                     | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs_sticky_bit
                                                     [1U]) 
                                                    << 1U))) 
            ^ ((- (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                          [1U])) << 1U)) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
           [1U]);
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2[1U] 
        = __Vtemp_h4472ca76__0[1U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2[2U] 
        = __Vtemp_h4472ca76__0[2U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2[3U] 
        = __Vtemp_h4472ca76__0[3U];
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2[4U] 
        = __Vtemp_h4472ca76__0[4U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_fflags[0U][1U] 
        = (0x1fU & ((0x20U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U])
                     ? ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
                         << 0x1fU) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
                                      >> 1U)) : (((
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
                                                   << 0x1fU) 
                                                  | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[2U] 
                                                     >> 1U)) 
                                                 | (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__overflowExp) 
                                                     << 2U) 
                                                    | (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__underflowExp) 
                                                        << 1U) 
                                                       | (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__overflowExp))))));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet[0U] 
        = ((0xf00000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
            [0U]) | (IData)((IData)(((5U >= vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                      [0U]) ? vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd
                                     [0U][vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                     [0U]] : 0U))));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet[1U] 
        = ((0xf00000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
            [1U]) | (IData)((IData)(((5U >= vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                      [1U]) ? vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd
                                     [1U][vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                     [1U]] : 0U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_taken)
            ? (((0x1000000U & vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U])
                 ? ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[4U] 
                     << 1U) | (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[3U] 
                               >> 0x1fU)) : ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U] 
                                              << 5U) 
                                             | (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U] 
                                                >> 0x1bU))) 
               + VL_EXTENDS_II(32,21, (0x1fffffU & 
                                       vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[0U])))
            : ((vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[2U] 
                << 2U) | (vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs[1U] 
                          >> 0x1eU)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__ras_block__DOT__ri_fifo.pop 
        = ((((vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U] 
              >> 2U) & (vlSelf->taiga_sim__DOT__cpu__DOT__br_results[2U] 
                        >> 4U)) & ((IData)(taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex) 
                                   >> 2U)) & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__inflight_count) 
                                              >> 3U));
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_update_way 
        = (3U & ((- (IData)((1U & (vlSelf->taiga_sim__DOT__cpu__DOT__br_results[2U] 
                                   >> 4U)))) & (IData)(taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex)));
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry 
        = ((0x7ffffcU & vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry) 
           | ((0x10U & (IData)(taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex))
               ? ((8U & (IData)(taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex))
                   ? ((8U & vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U])
                       ? 3U : 2U) : ((8U & vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U])
                                      ? 3U : 1U)) : 
              ((8U & (IData)(taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex))
                ? ((8U & vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U])
                    ? 2U : 0U) : ((8U & vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U])
                                   ? 1U : 0U))));
    if ((1U & (~ ((IData)(taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex) 
                  >> 2U)))) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry 
            = ((0x7ffffcU & vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry) 
               | ((8U & vlSelf->taiga_sim__DOT__cpu__DOT__br_results[0U])
                   ? 3U : 0U));
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__rst 
        = (1U & ((IData)(vlSelf->rst) | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                         >> 0xcU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__flush_or_rst 
        = (1U & (((IData)(vlSelf->rst) | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                          >> 0xeU)) 
                 | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__early_branch_flush)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list.potential_push 
        = (1U & (((vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                   >> 0x12U) & (~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index) 
                                   >> 5U))) | (IData)(
                                                      (0x80U 
                                                       == 
                                                       (0x82U 
                                                        & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__retire))))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list.potential_push 
        = (1U & (((vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                   >> 0x12U) & (~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index) 
                                   >> 5U))) | (IData)(
                                                      (0x82U 
                                                       == 
                                                       (0x82U 
                                                        & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__retire))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT____Vcellinp__read_index_fifo__rst 
        = (1U & (((IData)(vlSelf->rst) | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                          >> 0xeU)) 
                 | ((((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__valid_fetch_result) 
                      & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram.data_valid)) 
                     & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_fifo.data_out) 
                        >> 3U)) & (~ (IData)(taiga_sim__DOT__cpu__DOT__fetch_block__DOT__is_branch_or_jump)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_no_id_stall 
        = (((~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                >> 0xcU)) & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__inflight_count) 
                             >> 3U)) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                           >> 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[1U] 
        = (1U & (((vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                   >> 0xcU) & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                               >> 0xaU)) & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                            >> 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_mux[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__gc[0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_retire_port_valid[0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_port_valid
           [0U] & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                      >> 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_retire_port_valid[1U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_port_valid
           [1U] & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                      >> 0xdU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request 
        = (1U & (((~ ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__inflight_count) 
                      >> 3U)) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                    >> 0x11U))) & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__exception_pending))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rollback 
        = ((IData)(((vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                     >> 0xeU) & (0x81000U == (0x81000U 
                                              & vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U])))) 
           & (0U != (0x1fU & ((vlSelf->taiga_sim__DOT__cpu__DOT__issue[2U] 
                               << 4U) | (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                                         >> 0x1cU)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rollback 
        = (1U & (((vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                   >> 0xeU) & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                               >> 0xcU)) & (vlSelf->taiga_sim__DOT__cpu__DOT__issue[0U] 
                                            >> 0xaU)));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest_one_hot = 0U;
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest_one_hot 
        = ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest_one_hot) 
           | (0xfU & ((IData)(1U) << (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__issued_one_hot 
        = ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest_one_hot) 
           & (- (IData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_ack))));
    vlSelf->data_bram_addr = (0x1fffffffU & ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[4U] 
                                              << 0xfU) 
                                             | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
                                                >> 0x11U)));
    vlSelf->data_bram_be = (0xfU & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
                                    >> 8U));
    vlSelf->data_bram_we = ((2U & vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[2U]) 
                            | (1U & vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[0U]));
    vlSelf->data_bram_data_in = ((2U & vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[2U])
                                  ? (((QData)((IData)(
                                                      ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[1U] 
                                                        << 0x1fU) 
                                                       | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[0U] 
                                                          >> 1U)))) 
                                      << 0x20U) | (QData)((IData)(
                                                                  ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[2U] 
                                                                    << 0x1fU) 
                                                                   | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[1U] 
                                                                      >> 1U)))))
                                  : (QData)((IData)(
                                                    ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
                                                      << 0x1bU) 
                                                     | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[2U] 
                                                        >> 5U)))));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes.push 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__issue_request) 
           & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
              >> 0xdU));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes_in 
        = ((3U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes_in)) 
           | (((0x700U & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
                          << 3U)) | (0xc0U & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
                                              >> 8U))) 
              | ((0x20U & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[2U] 
                           << 4U)) | (0x1cU & vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[2U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes_in 
        = ((0x7feU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes_in)) 
           | (1U & vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[0U]));
    __Vfunc_address_range_check__6__addr = ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[4U] 
                                             << 0x12U) 
                                            | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
                                               >> 0xeU));
    __Vfunc_address_range_check__6__Vfuncout = (8U 
                                                == 
                                                (__Vfunc_address_range_check__6__addr 
                                                 >> 0x1cU));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match)) 
           | (IData)(__Vfunc_address_range_check__6__Vfuncout));
    __Vfunc_address_range_check__7__addr = ((vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[4U] 
                                             << 0x12U) 
                                            | (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq.transaction_out[3U] 
                                               >> 0xeU));
    __Vfunc_address_range_check__7__Vfuncout = (6U 
                                                == 
                                                (__Vfunc_address_range_check__7__addr 
                                                 >> 0x1cU));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match 
        = ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match)) 
           | ((IData)(__Vfunc_address_range_check__7__Vfuncout) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__possible_subnormal[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__right_shift
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[0U] 
        = ((0xe001ffffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[0U]) 
           | (0xfffe0000U & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit
                               [2U] << 0x1cU) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm
                                                  [2U] 
                                                  << 0x19U) 
                                                 | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__instruction
                                                     [2U] 
                                                     << 0x16U) 
                                                    | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation
                                                       [2U] 
                                                       << 0x15U)))) 
                             | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf
                                 [2U] << 0x14U) | (
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN
                                                    [2U] 
                                                    << 0x12U) 
                                                   | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero
                                                      [2U] 
                                                      << 0x11U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__special_case_results[0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf
           [3U] ? (0x7ff0000000000000ULL | ((QData)((IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign
                                                            [1U])) 
                                            << 0x3fU))
            : (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN
               [3U] ? 0x7ff8000000000000ULL : (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero
                                               [3U]
                                                ? ((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign
                                                                   [1U])) 
                                                   << 0x3fU)
                                                : ((QData)((IData)(
                                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign
                                                                   [1U])) 
                                                   << 0x3fU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo[0U] 
        = (0xfffU & (((0x1000U & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo_intermediate))
                       ? (0x1fffU & (- (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo_intermediate)))
                       : (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo_intermediate)) 
                     & (- (IData)((1U & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero
                                         [2U]))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case[0U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf
            [2U] | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN
            [2U]) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero
           [2U]);
    if ((1U & (~ VL_ONEHOT0_I(((2U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed) 
                                      >> 4U)) | (1U 
                                                 & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed) 
                                                    >> 1U))))))) {
        if (VL_UNLIKELY(vlSymsp->_vm_contextp__->assertOn())) {
            VL_WRITEF("[%0t] %%Error: decode_and_issue.sv:232: Assertion failed in %Ntaiga_sim.cpu.decode_and_issue_block: synthesis parallel_case, but multiple matches found\n",
                      64,VL_TIME_UNITED_Q(1),-12,vlSymsp->name());
            VL_STOP_MT("/localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/taiga-project/../core/decode_and_issue.sv", 232, "");
        }
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_exception_unit 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed))
            ? 0U : ((0x20U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed))
                     ? 1U : 2U));
    if (vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__illegal_instruction_pattern) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_exception_unit = 2U;
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[0U] 
        = ((0x7eU & vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux
            [0U]) | (1U & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__greater_than_largest_unsigned_int 
        = (1U & ((~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                     >> 0x1cU)) & ((((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int 
                                      >> 0x1fU) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__largest_unsigned_int)) 
                                    & (0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__grs))) 
                                   | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                      >> 0x1eU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__greater_than_largest_signed_int 
        = (1U & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                   >> 0x1cU) & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[9U] 
                                   >> 0xbU))) & (((
                                                   (~ 
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int 
                                                     >> 0x1fU)) 
                                                   & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__largest_signed_int)) 
                                                  & (0U 
                                                     != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__grs))) 
                                                 | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                                    >> 0x1dU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smaller_than_smallest_signed_int 
        = (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
             >> 0x1cU) & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[9U] 
                          >> 0xbU)) & (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int 
                                         >> 0x1fU) 
                                        & ((~ (IData)(
                                                      (0U 
                                                       != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR)))) 
                                           | (0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__grs)))) 
                                       | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                          >> 0x1eU)));
    __Vtableidx2 = ((0x80U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int 
                              << 7U)) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__grs) 
                                          << 4U) | 
                                         ((8U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[9U] 
                                                 >> 8U)) 
                                          | (7U & (
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed[6U] 
                                                   >> 0x18U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__roundup 
        = Vtaiga_sim__ConstPool__TABLE_hbdb5e6c2_0[__Vtableidx2];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf[0U] 
        = (1U & ((IData)((0U != (0x22000000U & taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fp_add_inputs[3U]))) 
                 & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN
                    [0U])));
    VL_EXTEND_WW(161,160, __Vtemp_h4a9d8ffe__0, taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1);
    VL_EXTEND_WW(161,160, __Vtemp_h7a991c01__0, taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2);
    VL_ADD_W(6, __Vtemp_h558c6d26__0, __Vtemp_h4a9d8ffe__0, __Vtemp_h7a991c01__0);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__adder_carry_out 
        = (1U & __Vtemp_h558c6d26__0[5U]);
    VL_EXTEND_WW(161,160, __Vtemp_h4a9d8ffe__1, taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1);
    VL_EXTEND_WW(161,160, __Vtemp_h7a991c01__1, taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2);
    VL_ADD_W(6, __Vtemp_h4edd94c7__0, __Vtemp_h4a9d8ffe__1, __Vtemp_h7a991c01__1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_intermediate[0U] 
        = ((__Vtemp_h4edd94c7__0[1U] << 0x1fU) | (__Vtemp_h4edd94c7__0[0U] 
                                                  >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_intermediate[1U] 
        = ((__Vtemp_h4edd94c7__0[2U] << 0x1fU) | (__Vtemp_h4edd94c7__0[1U] 
                                                  >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_intermediate[2U] 
        = ((__Vtemp_h4edd94c7__0[3U] << 0x1fU) | (__Vtemp_h4edd94c7__0[2U] 
                                                  >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_intermediate[3U] 
        = (0xffU & (__Vtemp_h4edd94c7__0[3U] >> 1U));
    taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_hcae1b096__0 
        = (0U != vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done
           [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet[0U][2U] 
        = ((0xeU & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet
            [0U][2U]) | (0xfU & (IData)(taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_hcae1b096__0)));
    taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_hcd32a4c9__0 
        = ((5U >= (7U & ((IData)(3U) * vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel
                         [0U]))) ? (7U & (vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_instruction_id
                                          [0U] >> (7U 
                                                   & ((IData)(3U) 
                                                      * 
                                                      vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel
                                                      [0U]))))
            : 0U);
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet[0U][2U] 
        = ((1U & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet
            [0U][2U]) | (0xfU & ((IData)(taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_hcd32a4c9__0) 
                                 << 1U)));
    taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_h841830c4__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_rd
        [0U][vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet[0U][0U] 
        = (IData)(taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_h841830c4__0);
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet[0U][1U] 
        = (IData)((taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_h841830c4__0 
                   >> 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_ack[0U] = 0U;
    taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_h41f75b63__0 
        = (1U & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet
           [0U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_ack[0U] 
        = (((~ ((IData)(1U) << vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel
                [0U])) & vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_ack
            [0U]) | (3U & ((IData)(taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT____Vlvbound_h41f75b63__0) 
                           << vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel
                           [0U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_unit_fflag_wb_packet 
        = ((0x1fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_unit_fflag_wb_packet)) 
           | ((0x100U & (vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet
                         [0U][2U] << 8U)) | (0xe0U 
                                             & (vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet
                                                [0U][2U] 
                                                << 4U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_unit_fflag_wb_packet 
        = ((0x1e0U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_unit_fflag_wb_packet)) 
           | vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_fflags
           [0U][vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel
           [0U]]);
    vlSelf->taiga_sim__DOT__cpu__DOT__unit_fflag_wb_packet 
        = ((0x1fU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__unit_fflag_wb_packet)) 
           | ((0x100U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
                                  [1U] >> 0x20U)) << 8U)) 
              | (0xe0U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
                                   [1U] >> 0x21U)) 
                          << 5U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack[0U] = 0U;
    taiga_sim__DOT__cpu__DOT__writeback_block__DOT____Vlvbound_h84ca567e__0 
        = (1U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
                         [0U] >> 0x20U)));
    if ((5U >= vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
         [0U])) {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack[0U] 
            = (((~ ((IData)(1U) << vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                    [0U])) & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack
                [0U]) | (0x3fU & ((IData)(taiga_sim__DOT__cpu__DOT__writeback_block__DOT____Vlvbound_h84ca567e__0) 
                                  << vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                  [0U])));
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack[1U] = 0U;
    taiga_sim__DOT__cpu__DOT__writeback_block__DOT____Vlvbound_h84ca567e__0 
        = (1U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
                         [1U] >> 0x20U)));
    if ((5U >= vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
         [1U])) {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack[1U] 
            = (((~ ((IData)(1U) << vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                    [1U])) & vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack
                [1U]) | (0x3fU & ((IData)(taiga_sim__DOT__cpu__DOT__writeback_block__DOT____Vlvbound_h84ca567e__0) 
                                  << vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel
                                  [1U])));
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__wb_packet[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__wb_packet[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__target_update_way 
        = ((- (IData)((1U & ((~ ((IData)(taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex) 
                                 >> 2U)) | (((IData)(taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_ex) 
                                             >> 4U) 
                                            ^ (vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry 
                                               >> 1U)))))) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_update_way));
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_no_instruction_stall 
        = (1U & (((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__tr_no_id_stall)) 
                  & (~ (vlSelf->taiga_sim__DOT__cpu__DOT__issue[1U] 
                        >> 0xcU))) | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                      >> 0xeU)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__next_pc 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_mux
        [(3U & (vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__encoder_rom 
                >> (0x1fU & (0x10U | ((((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches)) 
                                        & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__early_branch_flush))) 
                                       << 3U) | (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_flush) 
                                                  << 2U) 
                                                 | (2U 
                                                    & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[1U] 
                                                       << 1U))))))))];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_retire_port_valid
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_retire_port_valid
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__update_pc 
        = (1U & (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request) 
                  | (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                     >> 0xeU)) | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__early_branch_flush)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__ras.branch_fetched 
        = ((((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches)) 
             & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__bp.is_branch)) 
            & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request)) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__early_branch_flush)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram.new_request 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__sub_unit_address_match));
    vlSelf->taiga_sim__DOT__cpu__DOT__pc_id_assigned 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request) 
           | (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__itlb.is_fault));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__ras.push 
        = ((((((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches)) 
               & ((0x2dU >= (0x3fU & ((IData)(2U) + 
                                      ((IData)(0x17U) 
                                       * (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way))))) 
                  & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry 
                             >> (0x3fU & ((IData)(2U) 
                                          + ((IData)(0x17U) 
                                             * (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way)))))))) 
              & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_flush))) 
             & (~ vlSelf->taiga_sim__DOT__cpu__DOT__gc[1U])) 
            & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request)) 
           & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__early_branch_flush)));
    taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot 
        = ((8U & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                  >> 0xfU)) | ((4U & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                      >> 0xbU)) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rollback) 
                                                   << 1U)));
    taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot 
        = ((8U & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                  >> 0xfU)) | ((4U & (vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                                      >> 0xbU)) | ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rollback) 
                                                   << 1U)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bus.new_request 
        = (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match) 
            >> 1U) & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__issue_request));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bram.new_request 
        = ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__issue_request));
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellout__sub_unit_select__int_out 
        = ((2U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match))
            ? 1U : 0U);
    taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellout__sub_unit_select__int_out 
        = (1U & ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellout__sub_unit_select__int_out) 
                 | ((1U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match))
                     ? 0U : 0U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[6U] 
        = ((0xfffffc7fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[6U]) 
           | (0xffffff80U & ((0x200U & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                                        [0U] >> 2U)) 
                             | ((0x100U & ((IData)(
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                    [0U] 
                                                    >> 0x34U)) 
                                           << 8U)) 
                                | (0x80U & ((IData)(
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                     [0U] 
                                                     >> 0x35U)) 
                                            << 7U))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[0U] 
        = ((0x1fU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[0U]) 
           | ((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign
                                        [0U])) << 0x3fU) 
                       | (((QData)((IData)((0x7ffU 
                                            & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                                            [0U]))) 
                           << 0x34U) | (0xfffffffffffffULL 
                                        & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                        [0U])))) << 5U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[1U] 
        = (((IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign
                                      [0U])) << 0x3fU) 
                     | (((QData)((IData)((0x7ffU & 
                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                                          [0U]))) << 0x34U) 
                        | (0xfffffffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                           [0U])))) >> 0x1bU) | ((IData)(
                                                         ((((QData)((IData)(
                                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign
                                                                            [0U])) 
                                                            << 0x3fU) 
                                                           | (((QData)((IData)(
                                                                               (0x7ffU 
                                                                                & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                                                                                [0U]))) 
                                                               << 0x34U) 
                                                              | (0xfffffffffffffULL 
                                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                                 [0U]))) 
                                                          >> 0x20U)) 
                                                 << 5U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[2U] 
        = (0x1ffU & (((IData)(((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign
                                                 [0U])) 
                                 << 0x3fU) | (((QData)((IData)(
                                                               (0x7ffU 
                                                                & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                                                                [0U]))) 
                                               << 0x34U) 
                                              | (0xfffffffffffffULL 
                                                 & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                 [0U]))) 
                               >> 0x20U)) >> 0x1bU) 
                     | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id
                         [1U] << 6U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done
                                        [1U] << 5U))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__expo_diff 
        = (0x1fffU & (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                      [0U] - ((0x7ffU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3
                                                 [2U] 
                                                 >> 0x34U))) 
                              + (1U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit
                                        [2U]) & (~ 
                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case
                                                 [2U]))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][3U] 
        = (0xffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
           [0U][3U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][4U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
            [1U] ? 0U : ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                 [1U]) << 0x14U)) << 8U);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][5U] 
        = (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
             [1U] ? 0U : ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                  [1U]) << 0x14U)) 
            >> 0x18U) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                          [1U] ? 0U : (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                                [1U]) 
                                        >> 0xcU) | 
                                       ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                                 [1U] 
                                                 >> 0x20U)) 
                                        << 0x14U))) 
                         << 8U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][6U] 
        = ((0xffff0000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
            [0U][6U]) | (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                           [1U] ? 0U : (((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                                 [1U]) 
                                         >> 0xcU) | 
                                        ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                                  [1U] 
                                                  >> 0x20U)) 
                                         << 0x14U))) 
                          >> 0x18U) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                                        [1U] ? 0U : 
                                        ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs
                                                  [1U] 
                                                  >> 0x20U)) 
                                         >> 0xcU)) 
                                       << 8U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal[0U] 
        = ((0xdU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal
            [0U]) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__possible_subnormal
                      [1U] & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                              [1U])) << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow[0U] 
        = ((0xdU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow
            [0U]) | (2U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                            [1U] >> 0xaU) & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                                              [1U]) 
                                             << 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift[0U] 
        = ((0xdU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift
            [0U]) | (2U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__right_shift
                            [1U] | ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                             [1U] >> 0x35U)) 
                                    & (~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                                       [1U]))) << 1U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt[0U] 
        = ((0xfffffc007ffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt
            [0U]) | ((QData)((IData)((0x7ffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__possible_subnormal
                                                 [1U] 
                                                 & (~ 
                                                    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
                                                    [1U]))
                                                 ? 
                                                (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                                                 [1U] 
                                                 + 
                                                 vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__possible_subnormal
                                                 [1U])
                                                 : 
                                                (1U 
                                                 & (IData)(
                                                           (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                                                            [1U] 
                                                            >> 0x35U))))))) 
                     << 0xbU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd[0U][1U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case
           [1U] ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__special_case_results
           [0U] : (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign
                                    [1U])) << 0x3fU) 
                   | (((QData)((IData)((0x7ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                                        [1U]))) << 0x34U) 
                      | (0xfffffffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac
                         [1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case[0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf
           [1U] | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN
           [1U]);
    VL_EXTEND_WW(161,160, __Vtemp_h4a9d8ffe__2, taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in1);
    VL_EXTEND_WW(161,160, __Vtemp_h7a991c01__2, taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__in2);
    VL_ADD_W(6, __Vtemp_h6d43b682__0, __Vtemp_h4a9d8ffe__2, __Vtemp_h7a991c01__2);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac[0U] 
        = (0x7fffffffffffffULL & (((QData)((IData)(
                                                   (0x7fffffffU 
                                                    & ((((IData)(
                                                                 (0x7fffffffffffffULL 
                                                                  & (((QData)((IData)(
                                                                                __Vtemp_h6d43b682__0[4U])) 
                                                                      << 0x17U) 
                                                                     | ((QData)((IData)(
                                                                                __Vtemp_h6d43b682__0[3U])) 
                                                                        >> 9U)))) 
                                                         >> 0x18U) 
                                                        | ((IData)(
                                                                   ((0x7fffffffffffffULL 
                                                                     & (((QData)((IData)(
                                                                                __Vtemp_h6d43b682__0[4U])) 
                                                                         << 0x17U) 
                                                                        | ((QData)((IData)(
                                                                                __Vtemp_h6d43b682__0[3U])) 
                                                                           >> 9U))) 
                                                                    >> 0x20U)) 
                                                           << 8U)) 
                                                       ^ 
                                                       (- (IData)(
                                                                  ((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__adder_carry_out)) 
                                                                   & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                                   [1U]))))))) 
                                   << 0x18U) | ((QData)((IData)(
                                                                ((((IData)(
                                                                           (0x7fffffffffffffULL 
                                                                            & (((QData)((IData)(
                                                                                __Vtemp_h6d43b682__0[4U])) 
                                                                                << 0x17U) 
                                                                               | ((QData)((IData)(
                                                                                __Vtemp_h6d43b682__0[3U])) 
                                                                                >> 9U)))) 
                                                                   << 8U) 
                                                                  | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_intermediate[3U]) 
                                                                 ^ 
                                                                 (- (IData)(
                                                                            ((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__adder_carry_out)) 
                                                                             & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                                                                             [1U])))))) 
                                                >> 8U)));
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_units_pending_wb 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_ack
           [0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_round 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_ack
                  [0U] >> 1U) | (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r[4U] 
                                    >> 9U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_wb_packet[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet
        [0U][0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_wb_packet[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet
        [0U][1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_wb_packet[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet
        [0U][2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div_ready 
        = (1U & ((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress)) 
                 | (vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack
                    [1U] >> 3U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__stage2_advance 
        = (1U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid
                  [1U]) | (vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack
                           [1U] >> 2U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__advance 
        = (1U & ((vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack
                  [1U] >> 4U) | (~ (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__unit_wb__BRA__5__KET__.done))));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__wb_packet
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__wb_packet
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = (0xeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = ((0xeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
           | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released) 
                    | (((7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids)) 
                        == vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids
                        [0U]) & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid
                       [0U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = ((0xeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
           | (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released) 
                    | (((7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids)) 
                        == vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids
                        [1U]) & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid
                       [1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = (0xdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = ((0xdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
           | (2U & ((0xfffffffeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
                    | ((((7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids) 
                                >> 3U)) == vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids
                         [0U]) & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid
                        [0U]) << 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = ((0xdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
           | (2U & ((0xfffffffeU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
                    | ((((7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids) 
                                >> 3U)) == vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids
                         [1U]) & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid
                        [1U]) << 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = (0xbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = ((0xbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
           | (4U & ((0xfffffffcU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
                    | ((((7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids) 
                                >> 6U)) == vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids
                         [0U]) & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid
                        [0U]) << 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = ((0xbU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
           | (4U & ((0xfffffffcU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
                    | ((((7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids) 
                                >> 6U)) == vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids
                         [1U]) & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid
                        [1U]) << 2U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = (7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = ((7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
           | (8U & ((0xfffffff8U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
                    | ((((7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids) 
                                >> 9U)) == vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids
                         [0U]) & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid
                        [0U]) << 3U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released 
        = ((7U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
           | (8U & ((0xfffffff8U & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released)) 
                    | ((((7U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids) 
                                >> 9U)) == vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids
                         [1U]) & vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid
                        [1U]) << 3U))));
    vlSelf->instruction_bram_en = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fetch_block__DOT__bram.new_request;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__new_index 
        = (7U & ((((IData)(((vlSelf->taiga_sim__DOT__cpu__DOT__gc[3U] 
                             >> 0xeU) & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__inflight_count) 
                                         >> 3U))) ? 
                   vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram
                   [vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index]
                    : (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index)) 
                  + (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__ras.push)) 
                 - ((((((0U != (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches)) 
                        & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__bp.is_return)) 
                       & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__branch_flush))) 
                      & (~ vlSelf->taiga_sim__DOT__cpu__DOT__gc[1U])) 
                     & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request)) 
                    & (~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__early_branch_flush)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel 
        = ((8U & (IData)(taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot))
            ? 3U : 0U);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel 
        = (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel) 
                 | ((4U & (IData)(taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot))
                     ? 2U : 0U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel 
        = (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel) 
                 | ((2U & (IData)(taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot))
                     ? 1U : 0U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel 
        = (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel) 
                 | ((1U & (IData)(taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot))
                     ? 0U : 0U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel 
        = ((8U & (IData)(taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot))
            ? 3U : 0U);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel 
        = (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel) 
                 | ((4U & (IData)(taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot))
                     ? 2U : 0U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel 
        = (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel) 
                 | ((2U & (IData)(taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot))
                     ? 1U : 0U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel 
        = (3U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel) 
                 | ((1U & (IData)(taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_sel_one_hot_to_int__one_hot))
                     ? 0U : 0U)));
    vlSelf->data_bram_en = vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__bram.new_request;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes_in 
        = ((0x7fdU & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes_in)) 
           | ((IData)(taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellout__sub_unit_select__int_out) 
              << 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[6U] 
        = ((0x3ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[6U]) 
           | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[0U] 
              << 0xaU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[7U] 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[0U] 
            >> 0x16U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[1U] 
                         << 0xaU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[8U] 
        = ((0x80000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[8U]) 
           | (0xfffffU & ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[1U] 
                           >> 0x16U) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb[2U] 
                                        << 0xaU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[0U] 
        = ((0xffffe000U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs[0U]) 
           | ((0x1ffeU & (((0x1000U & (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__expo_diff))
                            ? (((0x7ffU & (IData)((
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3
                                                   [2U] 
                                                   >> 0x34U))) 
                                + (1U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit
                                          [2U]) & (~ 
                                                   vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case
                                                   [2U])))) 
                               - vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo
                               [0U]) : (IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__expo_diff)) 
                          << 1U)) | (1U & ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__expo_diff) 
                                           >> 0xcU))));
    if (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case
        [1U]) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][0U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][1U] = 0U;
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][2U] = 0U;
    } else {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][0U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[0U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][1U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[1U];
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][2U] 
            = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[2U];
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[0U][3U] 
        = ((0xffffff00U & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs
            [0U][3U]) | (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case
                         [1U] ? 0U : vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[3U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry[0U] 
        = ((0xeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry
            [0U]) | (1U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                   [1U] >> 0x36U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe[0U] 
        = ((0xeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe
            [0U]) | (1U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                   [1U] >> 0x35U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden[0U] 
        = ((0xeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden
            [0U]) | (1U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                   [1U] >> 0x34U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift[0U] 
        = ((0xeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift
            [0U]) | (1U & ((IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                    [1U] >> 0x36U)) 
                           | (IData)((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                      [1U] >> 0x35U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt[0U] 
        = ((0xffffffff800ULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt
            [0U]) | (IData)((IData)(((2U & ((IData)(
                                                    (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                                     [1U] 
                                                     >> 0x36U)) 
                                            << 1U)) 
                                     | (1U & ((~ (IData)(
                                                         (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                                          [1U] 
                                                          >> 0x36U))) 
                                              & (IData)(
                                                        (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                                         [1U] 
                                                         >> 0x35U))))))));
    taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_zero 
        = (1U & (((~ (IData)((0U != vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff
                              [2U]))) | ((1U == vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff
                                          [2U]) & (IData)(
                                                          (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac
                                                           [2U] 
                                                           >> 0x35U)))) 
                 & ((~ (IData)((0U != vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                                [1U]))) & (~ (IData)(
                                                     (0U 
                                                      != 
                                                      (((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[0U] 
                                                         | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[1U]) 
                                                        | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[2U]) 
                                                       | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[3U])))))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input 
        = ((0U != vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
            [1U]) ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
           [1U] : (0xfffffffffffffULL & (((QData)((IData)(
                                                          vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[3U])) 
                                          << 0x2cU) 
                                         | (((QData)((IData)(
                                                             vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[2U])) 
                                             << 0xcU) 
                                            | ((QData)((IData)(
                                                               vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs[1U])) 
                                               >> 0x14U)))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_shift 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_round) 
                 | (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r[6U] 
                       >> 4U))));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_wb_packet
        [0U][0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_wb_packet
        [0U][1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_wb_packet
        [0U][2U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.pop 
        = ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.valid) 
           & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div_ready));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div.start 
        = (((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.valid) 
            & (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div_ready)) 
           & (~ (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__input_fifo.data_out[0U] 
                 >> 3U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__stage1_advance 
        = (1U & ((~ vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid
                  [0U]) | (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__stage2_advance)));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__advance;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[1U] 
        = (1U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                         [1U] >> 0x20U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[1U] 
        = (7U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                         [1U] >> 0x21U)));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[0U] 
        = ((0x7fffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
            [0U]) | ((QData)((IData)((7U & (IData)(
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                                                    [0U] 
                                                    >> 0x21U))))) 
                     << 0x27U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[0U] 
        = ((0x3ff00000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
            [0U]) | (IData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                                    [0U])));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[1U] 
        = ((0x7fffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
            [1U]) | ((QData)((IData)((7U & (IData)(
                                                   (vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                                                    [1U] 
                                                    >> 0x21U))))) 
                     << 0x27U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[1U] 
        = ((0x3ff00000000ULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
            [1U]) | (IData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                                    [1U])));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__commit_phys_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table
        [(7U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                        [1U] >> 0x21U)))];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index_mux
        [vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index_mux
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel];
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo_overflow[1U] 
        = (1U & (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_zero)
                   ? 0U : ((vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo_overflow
                            [2U] << 0xbU) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo
                           [2U])) >> 0xbU));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo[1U] 
        = ((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_zero)
            ? 0U : (0x7ffU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo
                    [2U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_sign[1U] 
        = (((IData)(taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_zero) 
            & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
            [2U]) ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__zero_result_sign
           [2U] : (((~ (IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__r_adder_carry_out)) 
                    & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract
                    [2U]) ^ vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_sign
                   [2U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_norm 
        = (1U & ((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_shift) 
                 | (~ (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r[6U] 
                       >> 0xdU))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[2U] 
        = (1U & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet
           [0U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[2U] 
        = (7U & (vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet
                 [0U][2U] >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet
        [0U][0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet
        [0U][1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet
        [0U][2U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[0U] 
        = ((0x3c0ffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
            [0U]) | ((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__commit_phys_addr
                                     [0U])) << 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[1U] 
        = ((0x3c0ffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
            [1U]) | ((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__commit_phys_addr
                                     [1U])) << 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[0U] 
        = ((0x3bfffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
            [0U]) | ((QData)((IData)(((IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                                               [0U] 
                                               >> 0x20U)) 
                                      & (0U != vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__commit_phys_addr
                                         [0U])))) << 0x26U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[1U] 
        = ((0x3bfffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
            [1U]) | ((QData)((IData)(((IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet
                                               [1U] 
                                               >> 0x20U)) 
                                      & (0U != vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__commit_phys_addr
                                         [1U])))) << 0x26U));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow[0U] 
        = ((0xeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow
            [0U]) | vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo_overflow
           [1U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal[0U] 
        = ((0xeU & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal
            [0U]) | (1U & (~ (IData)((0U != vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo
                                      [1U])))));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__special_case_results[0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf
           [2U] ? (0x7ff0000000000000ULL | ((QData)((IData)(
                                                            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_sign
                                                            [1U])) 
                                            << 0x3fU))
            : (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN
               [2U] ? 0x7ff8000000000000ULL : 0ULL));
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd[0U][0U] 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case
           [1U] ? vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__special_case_results
           [0U] : (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_sign
                                    [1U])) << 0x3fU) 
                   | (((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo
                                       [1U])) << 0x34U) 
                      | (0xfffffffffffffULL & vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac
                         [1U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet[0U][2U] 
        = ((0x7fU & vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet
            [0U][2U]) | (0x380U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet
                                   [0U][2U] << 6U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet[0U][2U] 
        = ((0x3bfU & vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet
            [0U][2U]) | (0x40U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet
                                  [0U][2U] << 6U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet[0U][0U] 
        = (IData)((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet
                                    [0U][1U])) << 0x20U) 
                   | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet
                                     [0U][0U]))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet[0U][1U] 
        = (IData)(((((QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet
                                     [0U][1U])) << 0x20U) 
                    | (QData)((IData)(vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet
                                      [0U][0U]))) >> 0x20U));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__commit_phys_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table
        [(7U & (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet
                [0U][2U] >> 1U))];
    vlSelf->taiga_sim__DOT__cpu__DOT__commit_packet[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__commit_packet[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_ram__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_ram__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_ram__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet[0U][2U] 
        = ((0x3c0U & vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet
            [0U][2U]) | (0x3ffU & vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__commit_phys_addr
                         [0U]));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__commit[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__commit_packet
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__commit[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__commit_packet
        [1U];
    taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT____Vlvbound_h84bfe905__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_ram__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[0U] 
        = taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT____Vlvbound_h84bfe905__0;
    taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT____Vlvbound_h84bfe905__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_ram__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[1U] 
        = taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT____Vlvbound_h84bfe905__0;
    taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT____Vlvbound_h84bfe905__0 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_ram__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[2U] 
        = taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT____Vlvbound_h84bfe905__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__fp_commit_packet[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet
        [0U][0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__fp_commit_packet[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet
        [0U][1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__fp_commit_packet[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet
        [0U][2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[2U] 
        = (1U & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__commit
                         [1U] >> 0x26U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[2U] 
        = (0x3fU & (IData)((vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__commit
                            [1U] >> 0x20U)));
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [0U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [1U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [2U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram
        [vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr
        [3U]];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_commit_packet[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__fp_commit_packet
        [0U][0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_commit_packet[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__fp_commit_packet
        [0U][1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_commit_packet[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__fp_commit_packet
        [0U][2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
    taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_decode 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_data
            [2U] << 7U) | vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_data
           [1U]);
    taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_decode 
        = ((vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data
            [3U] << 0xeU) | ((vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data
                              [2U] << 7U) | vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data
                             [1U]));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__commit[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_commit_packet
        [0U][0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__commit[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_commit_packet
        [0U][1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__commit[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_commit_packet
        [0U][2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr
        [3U];
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.rs_wb_group 
        = ((2U & ((IData)(taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_decode) 
                  >> 6U)) | (1U & (IData)(taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_decode)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.phys_rs_addr 
        = ((0xfc0U & ((IData)(taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_decode) 
                      >> 2U)) | (0x3fU & ((IData)(taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_decode) 
                                          >> 1U)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface.rs_wb_group 
        = ((4U & (taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_decode 
                  >> 0xcU)) | ((2U & (taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_decode 
                                      >> 6U)) | (1U 
                                                 & taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_decode)));
    vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface.phys_rs_addr 
        = ((0x3f000U & (taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_decode 
                        >> 3U)) | ((0xfc0U & (taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_decode 
                                              >> 2U)) 
                                   | (0x3fU & (taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_decode 
                                               >> 1U))));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data
        [3U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[2U] 
        = (1U & (vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__commit
                 [0U][2U] >> 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[2U] 
        = (0x3fU & vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__commit
           [0U][2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_rs_wb_group[0U] 
        = (1U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.rs_wb_group));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_rs_wb_group[1U] 
        = (1U & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.rs_wb_group) 
                 >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_phys_rs_addr[0U] 
        = (0x3fU & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.phys_rs_addr));
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_phys_rs_addr[1U] 
        = (0x3fU & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__decode_rename_interface.phys_rs_addr) 
                    >> 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_rs_wb_group[0U] 
        = (1U & (IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface.rs_wb_group));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_rs_wb_group[1U] 
        = (1U & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface.rs_wb_group) 
                 >> 1U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_rs_wb_group[2U] 
        = (1U & ((IData)(vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface.rs_wb_group) 
                 >> 2U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_phys_rs_addr[0U] 
        = (0x3fU & vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface.phys_rs_addr);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_phys_rs_addr[1U] 
        = (0x3fU & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface.phys_rs_addr 
                    >> 6U));
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_phys_rs_addr[2U] 
        = (0x3fU & (vlSymsp->TOP__taiga_sim__DOT__cpu__DOT__fp_decode_rename_interface.phys_rs_addr 
                    >> 0xcU));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[0U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[1U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[2U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[3U][2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[3U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index;
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_rs_wb_group[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_rs_wb_group
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_rs_wb_group[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_rs_wb_group
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_phys_rs_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_phys_rs_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_rs_wb_group[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_rs_wb_group
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_rs_wb_group[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_rs_wb_group
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_rs_wb_group[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_rs_wb_group
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_phys_rs_addr[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_phys_rs_addr
        [0U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_phys_rs_addr[1U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_phys_rs_addr
        [1U];
    vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_phys_rs_addr[2U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_phys_rs_addr
        [2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [0U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [1U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [2U][0U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[0U] 
        = vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 
        = (vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use
           [0U] ^ vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data
           [3U][0U]);
}
