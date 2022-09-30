// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim___024root.h"

VL_ATTR_COLD void Vtaiga_sim___024root___initial__TOP__0(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___initial__TOP__0\n"); );
    // Init
    CData/*3:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__table_gen__0__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout;
    VlWide<3>/*95:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout;
    CData/*3:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__24__Vfuncout;
    IData/*31:0*/ __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout;
    IData/*31:0*/ __Vilp;
    // Body
    vlSelf->NUM_RETIRE_PORTS = 2U;
    vlSelf->write_uart = 0U;
    vlSelf->uart_byte = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0U;
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0xfU | __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout);
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x30U | (0xffffffc3U & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0xd0U | (0xffffff0fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x40U | (0xffffff3fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x300U | (0xfffffc3fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0xe00U | (0xfffff0ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x800U | (0xfffff3ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x3000U | (0xffffc3ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x2000U | (0xffffcfffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0xd000U | (0xffff0fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x8000U | (0xffff3fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x4000U | (0xffff3fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0xf0000U | (0xfff03fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x300000U | (0xffc3ffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0xd00000U | (0xff0fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x400000U | (0xff3fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x3000000U | (0xfc3fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0xe000000U | (0xf0ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x8000000U | (0xf3ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x30000000U | (0xc3ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x20000000U | (0xcfffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0xd0000000U | (0xfffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x80000000U | (0x3fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x40000000U | (0x3fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout 
        = (0x3fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__encoder_rom 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__table_gen__2__Vfuncout;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[0U] = 3U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[1U] = 2U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[2U] = 1U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[3U] = 1U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[0U] = 3U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[1U] = 2U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[2U] = 1U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[3U] = 1U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[0U] = 3U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[1U] = 2U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[2U] = 1U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[3U] = 1U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1fU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1eU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1dU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1cU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1bU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1aU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x19U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x18U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x17U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x16U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x15U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x14U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x13U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x12U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x11U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x10U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0U;
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank[__Vilp] = 0ULL;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0U;
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__1__KET____DOT__reg_group__DOT__register_file_bank[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vfunc_taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__table_gen__0__Vfuncout 
        = (3U | (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__table_gen__0__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__table_gen__0__Vfuncout 
        = (0xcU | (1U & (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__table_gen__0__Vfuncout)));
    __Vfunc_taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__table_gen__0__Vfuncout 
        = (7U & (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__table_gen__0__Vfuncout));
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__encoder_rom 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__table_gen__0__Vfuncout;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0ULL;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0ULL;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0ULL;
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0xfU | __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout);
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x30U | (0xffffffc3U & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0xd0U | (0xffffff0fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x40U | (0xffffff3fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x300U | (0xfffffc3fU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0xe00U | (0xfffff0ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x800U | (0xfffff3ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x3000U | (0xffffc3ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x2000U | (0xffffcfffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0xd000U | (0xffff0fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x8000U | (0xffff3fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x4000U | (0xffff3fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0xf0000U | (0xfff03fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x300000U | (0xffc3ffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0xd00000U | (0xff0fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x400000U | (0xff3fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x3000000U | (0xfc3fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0xe000000U | (0xf0ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x8000000U | (0xf3ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x30000000U | (0xc3ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x20000000U | (0xcfffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0xd0000000U | (0xfffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x80000000U | (0x3fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x40000000U | (0x3fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout 
        = (0x3fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__32__Vfuncout;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[0U] = 0U;
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vfunc_taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__24__Vfuncout 
        = (3U | (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__24__Vfuncout));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__24__Vfuncout 
        = (0xcU | (1U & (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__24__Vfuncout)));
    __Vfunc_taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__24__Vfuncout 
        = (7U & (IData)(__Vfunc_taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__24__Vfuncout));
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__24__Vfuncout;
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x24U | (0xffffffc0U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x100U | (0xfffffe07U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x840U | (0xfffff03fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x200U | (0xfffff1ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x4000U | (0xffff81ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x22000U | (0xfffc0fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x10000U | (0xfffc7fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x100000U | (0xffe07fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x80000U | (0xffe3ffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x840000U | (0xff03ffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x400000U | (0xff1fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x200000U | (0xff1fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x4000000U | (0xf81fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x23000000U | (0xc0ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x18000000U | (0xc7ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x7ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]);
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (1U | (0xfffffffeU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0xc0000000U | (0x3fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0xfffffffeU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]);
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U] 
        = (0x40000000U | (0x3fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (8U | (0xfffffff0U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (6U | (0xfffffff1U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (2U | (0xfffffff1U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x40U | (0xffffff81U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x30U | (0xffffff8fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x220U | (0xfffffc0fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x180U | (0xfffffc7fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x100U | (0xfffffc7fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x1000U | (0xffffe07fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0xc00U | (0xffffe3ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x800U | (0xffffe3ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x8400U | (0xffff03ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x6000U | (0xffff1fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x4000U | (0xffff1fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x2000U | (0xffff1fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x240000U | (0xffc01fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x1000000U | (0xfe07ffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x8400000U | (0xf03fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x2000000U | (0xf1ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x40000000U | (0x81ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x20000000U | (0xfffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (2U | (0xfffffffcU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x7fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]);
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (1U | (0xfffffffcU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U] 
        = (0x7fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U]);
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x10U | (0xffffffe0U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (8U | (0xffffffe3U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x84U | (0xffffff03U & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x40U | (0xffffff1fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x20U | (0xffffff1fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x400U | (0xfffff81fU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x2300U | (0xffffc0ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x1800U | (0xffffc7ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x10000U | (0xfffe07ffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0xc000U | (0xfffe3fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x84000U | (0xfff03fffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x60000U | (0xfff1ffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x20000U | (0xfff1ffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x400000U | (0xff81ffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x300000U | (0xff8fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x2200000U | (0xfc0fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x1800000U | (0xfc7fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x1000000U | (0xfc7fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x10000000U | (0xe07fffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0xc000000U | (0xe3ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x8000000U | (0xe3ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x84000000U | (0x3ffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x60000000U | (0x1fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x40000000U | (0x1fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x20000000U | (0x1fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]));
    __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U] 
        = (0x1fffffffU & __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U]);
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom[0U] 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[0U];
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom[1U] 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[1U];
    vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom[2U] 
        = __Vfunc_taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__table_gen__23__Vfuncout[2U];
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1fU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1eU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1dU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1cU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1bU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1aU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x19U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x18U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x17U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x16U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x15U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x14U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x13U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x12U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x11U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x10U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xfU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xeU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xdU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xcU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xbU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xaU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[9U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[8U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1fU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1eU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1dU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1cU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1bU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1aU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x19U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x18U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x17U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x16U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x15U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x14U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x13U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x12U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x11U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x10U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1fU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1eU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1dU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1cU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1bU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x1aU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x19U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x18U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x17U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x16U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x15U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x14U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x13U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x12U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x11U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0x10U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xfU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xeU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xdU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xcU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xbU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0xaU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[9U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[8U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[0U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1fU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1eU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1dU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1cU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1bU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x1aU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x19U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x18U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x17U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x16U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x15U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x14U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x13U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x12U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x11U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0x10U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xfU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xeU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xdU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xcU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xbU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0xaU] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[9U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[8U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[7U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[6U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[5U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[4U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[3U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[2U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[1U] = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[0U] = 0U;
    __Vilp = 0U;
    while ((__Vilp <= 0x1ffU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__0__KET____DOT__tag_bank__DOT__branch_ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x1ffU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__1__KET____DOT__tag_bank__DOT__branch_ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x1ffU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__0__KET____DOT__addr_table__DOT__branch_ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x1ffU)) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__1__KET____DOT__addr_table__DOT__branch_ram[__Vilp] = 0U;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__last_unit = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index = 0U;
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index = 0U;
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index = 0U;
}

VL_ATTR_COLD void Vtaiga_sim___024root___final(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___final\n"); );
}

VL_ATTR_COLD void Vtaiga_sim___024root___ctor_var_reset(Vtaiga_sim___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtaiga_sim___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->clk = VL_RAND_RESET_I(1);
    vlSelf->rst = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_araddr = VL_RAND_RESET_I(32);
    vlSelf->ddr_axi_arburst = VL_RAND_RESET_I(2);
    vlSelf->ddr_axi_arcache = VL_RAND_RESET_I(4);
    vlSelf->ddr_axi_arid = VL_RAND_RESET_I(6);
    vlSelf->ddr_axi_arlen = VL_RAND_RESET_I(8);
    vlSelf->ddr_axi_arlock = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_arprot = VL_RAND_RESET_I(3);
    vlSelf->ddr_axi_arqos = VL_RAND_RESET_I(4);
    vlSelf->ddr_axi_arready = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_arregion = VL_RAND_RESET_I(4);
    vlSelf->ddr_axi_arsize = VL_RAND_RESET_I(3);
    vlSelf->ddr_axi_arvalid = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_awaddr = VL_RAND_RESET_I(32);
    vlSelf->ddr_axi_awburst = VL_RAND_RESET_I(2);
    vlSelf->ddr_axi_awcache = VL_RAND_RESET_I(4);
    vlSelf->ddr_axi_awid = VL_RAND_RESET_I(6);
    vlSelf->ddr_axi_awlen = VL_RAND_RESET_I(8);
    vlSelf->ddr_axi_awlock = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_awprot = VL_RAND_RESET_I(3);
    vlSelf->ddr_axi_awqos = VL_RAND_RESET_I(4);
    vlSelf->ddr_axi_awready = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_awregion = VL_RAND_RESET_I(4);
    vlSelf->ddr_axi_awsize = VL_RAND_RESET_I(3);
    vlSelf->ddr_axi_awvalid = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_bid = VL_RAND_RESET_I(6);
    vlSelf->ddr_axi_bready = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_bresp = VL_RAND_RESET_I(2);
    vlSelf->ddr_axi_bvalid = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_rdata = VL_RAND_RESET_I(32);
    vlSelf->ddr_axi_rid = VL_RAND_RESET_I(6);
    vlSelf->ddr_axi_rlast = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_rready = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_rresp = VL_RAND_RESET_I(2);
    vlSelf->ddr_axi_rvalid = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_wdata = VL_RAND_RESET_I(32);
    vlSelf->ddr_axi_wlast = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_wready = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_wstrb = VL_RAND_RESET_I(4);
    vlSelf->ddr_axi_wvalid = VL_RAND_RESET_I(1);
    vlSelf->ddr_axi_wid = VL_RAND_RESET_I(6);
    vlSelf->addr = VL_RAND_RESET_I(30);
    vlSelf->be = VL_RAND_RESET_I(4);
    vlSelf->rnw = VL_RAND_RESET_I(1);
    vlSelf->is_amo = VL_RAND_RESET_I(1);
    vlSelf->amo_type_or_burst_size = VL_RAND_RESET_I(5);
    vlSelf->sub_id = VL_RAND_RESET_I(2);
    vlSelf->request_push = VL_RAND_RESET_I(1);
    vlSelf->request_full = VL_RAND_RESET_I(1);
    vlSelf->inv_addr = VL_RAND_RESET_I(30);
    vlSelf->inv_valid = VL_RAND_RESET_I(1);
    vlSelf->inv_ack = VL_RAND_RESET_I(1);
    vlSelf->con_result = VL_RAND_RESET_I(1);
    vlSelf->con_valid = VL_RAND_RESET_I(1);
    vlSelf->wr_data = VL_RAND_RESET_I(32);
    vlSelf->wr_data_push = VL_RAND_RESET_I(1);
    vlSelf->data_full = VL_RAND_RESET_I(1);
    vlSelf->rd_data = VL_RAND_RESET_I(32);
    vlSelf->rd_sub_id = VL_RAND_RESET_I(2);
    vlSelf->rd_data_valid = VL_RAND_RESET_I(1);
    vlSelf->rd_data_ack = VL_RAND_RESET_I(1);
    vlSelf->instruction_bram_addr = VL_RAND_RESET_I(30);
    vlSelf->instruction_bram_en = VL_RAND_RESET_I(1);
    vlSelf->instruction_bram_be = VL_RAND_RESET_I(4);
    vlSelf->instruction_bram_data_in = VL_RAND_RESET_I(32);
    vlSelf->instruction_bram_data_out = VL_RAND_RESET_I(32);
    vlSelf->data_bram_addr = VL_RAND_RESET_I(29);
    vlSelf->data_bram_we = VL_RAND_RESET_I(2);
    vlSelf->data_bram_en = VL_RAND_RESET_I(1);
    vlSelf->data_bram_be = VL_RAND_RESET_I(4);
    vlSelf->data_bram_data_in = VL_RAND_RESET_Q(64);
    vlSelf->data_bram_data_out = VL_RAND_RESET_Q(64);
    vlSelf->write_uart = VL_RAND_RESET_I(1);
    vlSelf->uart_byte = VL_RAND_RESET_I(8);
    vlSelf->NUM_RETIRE_PORTS = VL_RAND_RESET_I(32);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->retire_ports_instruction[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->retire_ports_pc[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->retire_ports_valid[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->store_queue_empty = VL_RAND_RESET_I(1);
    vlSelf->load_store_idle = VL_RAND_RESET_I(1);
    vlSelf->instruction_issued = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<26; ++__Vi0) {
        vlSelf->taiga_events[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->instruction_pc_dec = VL_RAND_RESET_I(32);
    vlSelf->debug_instructions = VL_RAND_RESET_Q(64);
    vlSelf->instruction_data_dec = VL_RAND_RESET_I(32);
    for (int __Vi0=0; __Vi0<53; ++__Vi0) {
        vlSelf->fp_taiga_events[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->LargeSigTrace[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__axi_arvalid = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__axi_awid = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__axi_awvalid = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__axi_wlast = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__axi_wvalid = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(90, vlSelf->taiga_sim__DOT__tr);
    VL_RAND_RESET_W(85, vlSelf->taiga_sim__DOT__fp_tr);
    vlSelf->taiga_sim__DOT__read_counter = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__begin_read_counter = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__write_counter = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__begin_write_counter = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_unit_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_no_id_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_no_instruction_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_other_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fls_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fdiv_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fsqrt_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fcmp_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fsign_inject_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fclass_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fcvt_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fls = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fmadd = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_fdiv_sqrt = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__operand_stall_due_to_wb2fp = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_stall_due_to_fmadd = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs1 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs2 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmadd_operand_stall_rs3 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall_rs1 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fadd_operand_stall_rs2 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall_rs1 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fmul_operand_stall_rs2 = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__fpu_tracer__DOT__stall_unit_onehot[__Vi0] = VL_RAND_RESET_I(5);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__fp_units_pending_wb = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__unit_done_r = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__fpu_tracer__DOT__unit_done_r_r = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__read_modify_write = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__address_phase_complete = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__amo_result = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__amo_result_r = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__read_count = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__amo_write_ready = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_reference_burst_count = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_in_progress = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_transfer_complete = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__pop = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__write_burst_count = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__l2_to_mem__DOT__on_last_burst = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__requests_in[__Vi0] = VL_RAND_RESET_Q(43);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__advance = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__arb_request = VL_RAND_RESET_Q(43);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_valid = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_lr = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_sc = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_store = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__requests[__Vi0] = VL_RAND_RESET_Q(43);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_request = VL_RAND_RESET_Q(43);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_id = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv_id_v = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__write_done = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__burst_count = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__input_data[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__return_push = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__l2_arb__DOT____Vcellout__reserv__abort = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__state = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__rr__DOT__muxes[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out = VL_RAND_RESET_Q(44);
    for (int __Vi0=0; __Vi0<16; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_Q(44);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation_address[__Vi0] = VL_RAND_RESET_I(30);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__address_match = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__reserv__DOT__revoke_reservation = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out = VL_RAND_RESET_I(7);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out = VL_RAND_RESET_I(32);
    for (int __Vi0=0; __Vi0<16; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<16; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_Q(35);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<16; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_Q(43);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<16; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__1__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_Q(43);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<16; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<16; ++__Vi0) {
        vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__1__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__0__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__l2_arb__DOT__genblk4__BRA__1__KET____DOT__inv_response_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    VL_RAND_RESET_W(72, vlSelf->taiga_sim__DOT__cpu__DOT__br_results);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_flush = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(173, vlSelf->taiga_sim__DOT__cpu__DOT__issue);
    VL_RAND_RESET_W(142, vlSelf->taiga_sim__DOT__cpu__DOT__alu_inputs);
    VL_RAND_RESET_W(160, vlSelf->taiga_sim__DOT__cpu__DOT__ls_inputs);
    VL_RAND_RESET_W(160, vlSelf->taiga_sim__DOT__cpu__DOT__branch_inputs);
    VL_RAND_RESET_W(66, vlSelf->taiga_sim__DOT__cpu__DOT__mul_inputs);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_inputs = VL_RAND_RESET_Q(41);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_inputs = VL_RAND_RESET_Q(48);
    VL_RAND_RESET_W(400, vlSelf->taiga_sim__DOT__cpu__DOT__fp_pre_processing_packet);
    vlSelf->taiga_sim__DOT__cpu__DOT__pc_id = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__pc_id_assigned = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_id = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_complete = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_instruction = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__early_branch_flush = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_advance = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(79, vlSelf->taiga_sim__DOT__cpu__DOT__decode);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_exception_unit = 0;
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_phys_rs_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_phys_rs_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_decode_rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__retire = VL_RAND_RESET_I(8);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__retire_ids[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__retire_port_valid[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__wb_packet[__Vi0] = VL_RAND_RESET_Q(36);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__commit_packet[__Vi0] = VL_RAND_RESET_Q(42);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(68, vlSelf->taiga_sim__DOT__cpu__DOT__fp_wb_packet[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(74, vlSelf->taiga_sim__DOT__cpu__DOT__fp_commit_packet[__Vi0]);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_unit_fflag_wb_packet = VL_RAND_RESET_I(9);
    vlSelf->taiga_sim__DOT__cpu__DOT__unit_fflag_wb_packet = VL_RAND_RESET_I(9);
    VL_RAND_RESET_W(115, vlSelf->taiga_sim__DOT__cpu__DOT__gc);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_idle = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__post_issue_count = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__epc = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__exception_target_pc = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__interrupt_taken = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__interrupt_pending = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__instruction_issued_with_rd = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_instruction_issued_with_rd = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__wb_snoop = VL_RAND_RESET_Q(36);
    VL_RAND_RESET_W(68, vlSelf->taiga_sim__DOT__cpu__DOT__fp_wb_snoop);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_operand_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_unit_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_no_id_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_no_instruction_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_alu_op = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_branch_or_jump_op = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_load_op = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_store_op = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_mul_op = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_div_op = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_misc_op = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_rs1_forwarding_needed = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_rs2_forwarding_needed = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__tr_rs1_and_rs2_forwarding_needed = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__retire_port_valid[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__retire_ids[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(74, vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__fp_commit_packet[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(68, vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__fp_wb_packet[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__id_block__commit_packet[__Vi0] = VL_RAND_RESET_Q(42);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__id_block__wb_packet[__Vi0] = VL_RAND_RESET_Q(36);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__fp_decode_phys_rs_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__decode_and_issue_block__decode_phys_rs_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__commit[__Vi0] = VL_RAND_RESET_Q(42);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__register_file_block__decode_phys_rs_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(74, vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__commit[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__fp_register_file_block__decode_phys_rs_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_port_valid[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__load_store_unit_block__retire_ids[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellinp__csr_unit_block__retire_ids[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__writeback_block__wb_packet[__Vi0] = VL_RAND_RESET_Q(36);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(68, vlSelf->taiga_sim__DOT__cpu__DOT____Vcellout__fp_writeback_block__wb_packet[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__uses_rd_table[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__fetch_metadata_table[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_id = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__oldest_pre_issue_id = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__fetched_count_neg = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pre_issue_count = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__pre_issue_count_next = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__post_issue_count_next = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__inflight_count = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_next = VL_RAND_RESET_I(8);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_ids_next[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_port_valid_next[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__decode_wb2_float = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_is_post_issue[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_ready_to_retire[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_id_uses_rd = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_wb2_float = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__retire_is_accu_fcsr = VL_RAND_RESET_I(2);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__commit_phys_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(74, vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellout__genblk1__DOT__fp_inst_id_management__fp_commit_packet[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(68, vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__fp_wb_packet[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__phys_addr_table[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT____Vcellinp__genblk1__DOT__fp_inst_id_management__retire_ids_next[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        for (int __Vi1=0; __Vi1<3; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[__Vi0][__Vi1] = VL_RAND_RESET_I(1);
        }
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index = VL_RAND_RESET_I(3);
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT____Vlvbound_hd6ac1f37__0 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_id_sel_encoder__DOT__genblk2__DOT__encoder_rom = VL_RAND_RESET_I(4);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__is_float_table[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_float_table[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__accu_fcsr_table[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_int_table[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__need_int_data_table[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_wb2_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_is_float = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fetch_accu_fcsr = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__commit_phys_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_I(4);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__sub_unit_address_match = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__unit_data_array[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__fetch_attr_next = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_mux[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__next_pc = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__flush_or_rst = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__update_pc = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__new_mem_request = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__exception_pending = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__valid_fetch_result = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fetch_block__DOT__pc_sel_encoder__DOT__genblk2__DOT__encoder_rom = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__if_entry = VL_RAND_RESET_Q(46);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__ex_entry = VL_RAND_RESET_I(23);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_table[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_if = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__predicted_pc = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_matches = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__replacement_way = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__tag_update_way = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__target_update_way = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__hit_way = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk1__DOT__branch_tag_banks__BRA__0__KET____DOT__tag_bank__read_data = VL_RAND_RESET_I(23);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk1__DOT__branch_tag_banks__BRA__1__KET____DOT__tag_bank__read_data = VL_RAND_RESET_I(23);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk2__DOT__branch_table_banks__BRA__0__KET____DOT__addr_table__read_data = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT____Vcellout__genblk2__DOT__branch_table_banks__BRA__1__KET____DOT__addr_table__read_data = VL_RAND_RESET_I(32);
    for (int __Vi0=0; __Vi0<512; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__0__KET____DOT__tag_bank__DOT__branch_ram[__Vi0] = VL_RAND_RESET_I(23);
    }
    for (int __Vi0=0; __Vi0<512; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__1__KET____DOT__tag_bank__DOT__branch_ram[__Vi0] = VL_RAND_RESET_I(23);
    }
    for (int __Vi0=0; __Vi0<512; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__0__KET____DOT__addr_table__DOT__branch_ram[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<512; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__1__KET____DOT__addr_table__DOT__branch_ram[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__new_index = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT____Vcellinp__read_index_fifo__rst = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__clear_index = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rename_valid = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__rollback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_addr[__Vi0] = VL_RAND_RESET_I(5);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_read_data[__Vi0] = VL_RAND_RESET_I(7);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_next_mux[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_previous_r = VL_RAND_RESET_I(7);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_update = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_write_index_mux[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_sel = VL_RAND_RESET_I(2);
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[__Vi0] = VL_RAND_RESET_I(7);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT____Vcellinp__spec_table_ram__raddr[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__lfsr_read_index__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__lut_ram[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__write_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__read_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__inflight_count = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out = VL_RAND_RESET_I(18);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_I(18);
    }
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__clear_index = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rename_valid = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__rollback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_addr[__Vi0] = VL_RAND_RESET_I(5);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_read_data[__Vi0] = VL_RAND_RESET_I(7);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_next_mux[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_previous_r = VL_RAND_RESET_I(7);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_update = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_write_index_mux[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_sel = VL_RAND_RESET_I(2);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellout__spec_table_ram__ram_data_out[__Vi0] = VL_RAND_RESET_I(7);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT____Vcellinp__spec_table_ram__raddr[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__lfsr_read_index__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__lut_ram[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__write_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__read_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__inflight_count = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out = VL_RAND_RESET_I(18);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_I(18);
    }
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__uses_rd = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fence = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_ifence = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_i2f = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_f2i = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_class = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fcmp = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_valid = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__operands_ready = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_operands_ready = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_needed_issue_stage = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__unit_ready = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_to = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__pre_issue_exception_pending = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__illegal_instruction_pattern = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_stage_ready = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__issue_rs_wb_group = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_imm_type = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__constant_alu = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_op = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_op_r = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_logic_op_r = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__alu_subtract = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__ls_offset = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_load_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_store_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_fence_r = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rd_to_id_table[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rs1_link = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rd_link = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_return = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_call = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__br_use_signed = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__pc_offset_r = VL_RAND_RESET_I(21);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__jalr = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_mret_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_sret_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__is_ifence_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__sys_op_match = VL_RAND_RESET_I(8);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__genblk6__DOT__prev_div_rs_addr = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__genblk6__DOT__prev_div_result_valid = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__unit_needed = VL_RAND_RESET_I(4);
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT____Vcellout__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__fp_decode_phys_rs_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_sign_inj = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_sign_inj_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_minmax = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_minmax_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_class_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_f2i_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_fcmp_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__uses_rs1 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_issue_rs_wb_group = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs1_conflict = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs2_conflict = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rs3_conflict = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__is_zero[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__hidden_bit[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rd_to_id_table[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        for (int __Vi1=0; __Vi1<2; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_data_set[__Vi0][__Vi1] = VL_RAND_RESET_I(32);
        }
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse_r[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__bypass[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellout__register_file_gen__BRA__1__KET____DOT__reg_group__data[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT____Vcellinp__register_file_gen__BRA__1__KET____DOT__reg_group__read_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        for (int __Vi1=0; __Vi1<5; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[__Vi0][__Vi1] = VL_RAND_RESET_I(1);
        }
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index = VL_RAND_RESET_I(6);
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__1__KET____DOT__reg_group__DOT__register_file_bank[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        for (int __Vi1=0; __Vi1<3; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_data_set[__Vi0][__Vi1] = VL_RAND_RESET_Q(64);
        }
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse_r[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__id_inuse_toggle_mem_set__in_use[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<6; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__read_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__id_inuse_toggle_mem_set__toggle[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__rs_wb_group[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__bypass[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellout__register_file_gen__BRA__0__KET____DOT__reg_group__data[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vcellinp__register_file_gen__BRA__0__KET____DOT__reg_group__read_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT____Vlvbound_h8712ac2e__0 = VL_RAND_RESET_Q(64);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___toggle[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___read_addr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        for (int __Vi1=0; __Vi1<7; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__read_data[__Vi0][__Vi1] = VL_RAND_RESET_I(1);
        }
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT___in_use[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__clear_index = VL_RAND_RESET_I(6);
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__0__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__0__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__1__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__1__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__2__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__2__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellout__write_port_gen__BRA__3__KET____DOT__mem__read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<7; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT____Vcellinp__write_port_gen__BRA__3__KET____DOT__mem__read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__lfsr_counter__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__0__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__1__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__2__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_data[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT___read_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellout__write_port__ram_data_out[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT____Vcellinp__write_port__raddr[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__id_inuse_toggle_mem_set__DOT__write_port_gen__BRA__3__KET____DOT__mem__DOT__write_port__DOT__xilinx_gen__DOT__ram[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<64; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank[__Vi0] = VL_RAND_RESET_Q(64);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_issued_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_taken = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__branch_taken_ex = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__id_ex = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__new_pc_ex = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__pc_ex = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__instruction_is_completing = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__jal_jalr_ex = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__is_return = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__is_call = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_a = VL_RAND_RESET_I(16);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_ls_b = VL_RAND_RESET_I(16);
    vlSelf->taiga_sim__DOT__cpu__DOT__branch_unit_block__DOT__bc__DOT__sub_eq_a = VL_RAND_RESET_I(16);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_switch_stall = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__ready_for_issue_from_lsq = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__issue_request = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__virtual_address = VL_RAND_RESET_I(32);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_array[__Vi0] = VL_RAND_RESET_Q(64);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_ready = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unit_data_valid = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__last_unit = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__unaligned_addr = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_exception_complete = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__sub_unit_address_match = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__fence_hold = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__load_attributes_in = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__be = VL_RAND_RESET_I(4);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_port_valid[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellinp__lsq_block__retire_ids[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT____Vcellout__genblk4__DOT__genblk1__DOT__axi_bus__data_out = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__addr_hash = VL_RAND_RESET_I(4);
    VL_RAND_RESET_W(149, vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lsq_entry);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__potential_store_conflicts = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__load_ack = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_full = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_entry = VL_RAND_RESET_Q(43);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_data = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_conflict = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__store_ack = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_output_valid = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_retire_port_valid[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_port_valid[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__retire_ids[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT____Vcellinp__sq_block__rst = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT____Vcellout__genblk1__DOT__write_port__ram_data_out = VL_RAND_RESET_Q(44);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_read_index__DOT__feedback = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback_input = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__lfsr_write_index__DOT__feedback = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram[__Vi0] = VL_RAND_RESET_Q(44);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__wb_snoop_r = VL_RAND_RESET_Q(36);
    VL_RAND_RESET_W(68, vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_wb_snoop_r);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__valid_next = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__hashes = VL_RAND_RESET_I(16);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__released = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__id_needed = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__ids = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count = VL_RAND_RESET_I(12);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_issue[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_issue[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_attr[__Vi0] = VL_RAND_RESET_Q(43);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__load_check_count_next = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_index_next = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__sq_oldest = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_request_one_hot = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__issued_one_hot = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_sq_request = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__new_load_waiting = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__waiting_load_completed = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__newly_released = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_h0412e4c3__0 = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT____Vlvbound_hc604ed0f__0 = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT__ready = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT____Vcellout__arvalid_m__result = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT____Vcellout__awvalid_m__result = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__genblk4__DOT__genblk1__DOT__axi_bus__DOT____Vcellout__wvalid_m__result = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__busy = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__commit = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__commit_in_progress = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__csr_inputs_r = VL_RAND_RESET_Q(48);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__selected_csr = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__selected_csr_r = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__updated_csr = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mwrite = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__uwrite = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle = VL_RAND_RESET_Q(33);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret = VL_RAND_RESET_Q(33);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_input_next = VL_RAND_RESET_Q(33);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_input_next = VL_RAND_RESET_Q(33);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__minst_ret_inc = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__mcycle_inc = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__fcsr = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_fcsr = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__csr_unit_block__DOT__next_frm = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state = 0;
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__next_state = 0;
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_init_clear = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_fetch_hold = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_issue_hold = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc_override = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__gc_pc = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state_counter = VL_RAND_RESET_I(7);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_ack[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_instruction_id[__Vi0] = VL_RAND_RESET_I(18);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_done[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        for (int __Vi1=0; __Vi1<6; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_rd[__Vi0][__Vi1] = VL_RAND_RESET_I(32);
        }
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        for (int __Vi1=0; __Vi1<6; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_fflags[__Vi0][__Vi1] = VL_RAND_RESET_I(5);
        }
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__unit_sel[__Vi0] = VL_RAND_RESET_I(3);
    }
    VL_RAND_RESET_W(96, vlSelf->taiga_sim__DOT__cpu__DOT__writeback_block__DOT__genblk3__BRA__1__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom);
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_ack[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_instruction_id[__Vi0] = VL_RAND_RESET_I(6);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_done[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        for (int __Vi1=0; __Vi1<2; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_rd[__Vi0][__Vi1] = VL_RAND_RESET_Q(64);
        }
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        for (int __Vi1=0; __Vi1<2; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_fflags[__Vi0][__Vi1] = VL_RAND_RESET_I(5);
        }
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__unit_sel[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fp_writeback_block__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__result = VL_RAND_RESET_Q(64);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__mulh[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__id[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__rs1_r = VL_RAND_RESET_Q(33);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__rs2_r = VL_RAND_RESET_Q(33);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__stage1_advance = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__stage2_advance = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_CLZ = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_CLZ = VL_RAND_RESET_I(5);
    VL_RAND_RESET_W(82, vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__fifo_inputs);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress_attr = VL_RAND_RESET_I(8);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__in_progress = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__div_ready = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__low_order_clz[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__sub_clz = VL_RAND_RESET_I(8);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__upper_lower[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__dividend_clz_block__DOT__clz_low_table[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__low_order_clz[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__sub_clz = VL_RAND_RESET_I(8);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__upper_lower[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divisor_clz_block__DOT__clz_low_table[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__CLZ_delta = VL_RAND_RESET_I(5);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__first_cycle_abort = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__shifted_divisor = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__new_quotient_bits = VL_RAND_RESET_I(2);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_1x = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_2x = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__sub_1x_overflow = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__cycles_remaining = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__cycles_remaining_next = VL_RAND_RESET_I(4);
    vlSelf->taiga_sim__DOT__cpu__DOT__genblk5__DOT__div_unit_block__DOT__divider_block__DOT__running = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(525, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inputs_pre_processed);
    VL_RAND_RESET_W(176, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_div_sqrt_inputs_pre_processed);
    VL_RAND_RESET_W(171, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2fp_misc_inputs_pre_processed);
    VL_RAND_RESET_W(300, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_wb2int_misc_inputs_pre_processed);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__new_request[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__id[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__ready[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1 = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2 = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs3 = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rm = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_i2f = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_f2i = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_class = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fcmp = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_minmax = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_sign_inj = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_opcode = VL_RAND_RESET_I(7);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_fn7 = VL_RAND_RESET_I(7);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_issue_id = VL_RAND_RESET_I(3);
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_inf[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_inf_swapped[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_SNaN[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_SNaN_swapped[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_QNaN[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_QNaN_swapped[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_zero[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_zero_swapped[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__hidden_bit[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_hidden_bit[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_subnormal[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_subnormal_swapped[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__expo_diff = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_expo_diff = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_expo_diff_negate = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_swap = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalize_shift_amt = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalize_shift_amt = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_pre_normalize_shift_amt = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_pre_normalize_shift_amt = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_hidden_bit_pre_normalized = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_hidden_bit_pre_normalized = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_frac_pre_normalized = VL_RAND_RESET_Q(52);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs2_frac_pre_normalized = VL_RAND_RESET_Q(52);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs1_pre_normalized_swapped = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__rs2_pre_normalized_swapped = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT____Vcellout__pre_normalize_rs1__frac_normalized = VL_RAND_RESET_Q(53);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT____Vcellout__pre_normalize_rs2__frac_normalized = VL_RAND_RESET_Q(53);
    VL_RAND_RESET_W(269, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__fp_add_inputs);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_fadd = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__is_fmul = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fma = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fadd = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_is_fmul = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_add = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_int_rs1 = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_sign = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_int_rs1_zero = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_is_signed = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_abs_rs1_expo_unbiased = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_f2i_int_less_than_1 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_31 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__r_rs1_expo_unbiased_greater_than_30 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__frac = VL_RAND_RESET_Q(53);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs1__DOT__clz_with_prepended_0s = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__frac = VL_RAND_RESET_Q(53);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_pre_processing_inst__DOT__pre_normalize_rs2__DOT__clz_with_prepended_0s = VL_RAND_RESET_I(11);
    VL_RAND_RESET_W(276, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs);
    VL_RAND_RESET_W(276, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_mul_outputs_r);
    VL_RAND_RESET_W(269, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__fma_add_inputs);
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode[__Vi0] = VL_RAND_RESET_I(7);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__instruction[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_sign[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_expo[__Vi0] = VL_RAND_RESET_I(11);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_frac[__Vi0] = VL_RAND_RESET_Q(53);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_sign[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_expo[__Vi0] = VL_RAND_RESET_I(11);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt[__Vi0] = VL_RAND_RESET_I(11);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_frac[__Vi0] = VL_RAND_RESET_Q(53);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo[__Vi0] = VL_RAND_RESET_I(12);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__possible_subnormal[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__right_shift[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac[__Vi0] = VL_RAND_RESET_Q(54);
    }
    VL_RAND_RESET_W(106, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac_intermediate);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__clz_with_prepended_0s = VL_RAND_RESET_I(11);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__special_case_results[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs[__Vi0] = VL_RAND_RESET_Q(52);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id[__Vi0] = VL_RAND_RESET_I(3);
    }
    VL_RAND_RESET_W(73, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__fma_mul_wb);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__mantissa_mul__DOT__rs1_r = VL_RAND_RESET_Q(53);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__mantissa_mul__DOT__rs2_r = VL_RAND_RESET_Q(53);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_sign[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo[__Vi0] = VL_RAND_RESET_I(11);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo_overflow[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac[__Vi0] = VL_RAND_RESET_Q(54);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac[__Vi0] = VL_RAND_RESET_Q(54);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__zero_result_sign[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_sign[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo[__Vi0] = VL_RAND_RESET_I(11);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_expo_overflow[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac[__Vi0] = VL_RAND_RESET_Q(55);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff[__Vi0] = VL_RAND_RESET_I(12);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned[__Vi0] = VL_RAND_RESET_Q(54);
    }
    VL_RAND_RESET_W(104, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_in);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        VL_RAND_RESET_W(104, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        VL_RAND_RESET_W(104, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs[__Vi0]);
    }
    VL_RAND_RESET_W(104, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<5; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__clz_with_prepended_0s = VL_RAND_RESET_I(11);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__special_case_results[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs_sticky_bit[__Vi0] = VL_RAND_RESET_I(1);
    }
    VL_RAND_RESET_W(104, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__grs_intermediate);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__adder_carry_out = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__r_adder_carry_out = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT____Vcellinp__genblk2__DOT__frac_clz__clz_input = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_QNaN = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__output_inf = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rm = VL_RAND_RESET_I(3);
    VL_RAND_RESET_W(84, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__fifo_inputs);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__in_progress = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT____Vcellinp__in_progress_m__set = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__in_progress_attr = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo = VL_RAND_RESET_I(12);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__result_frac[__Vi0] = VL_RAND_RESET_Q(53);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__grs[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__rs1_expo_r = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__done_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__genblk2__DOT__unbiased_expo = VL_RAND_RESET_I(12);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__running = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__terminate = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__counter = 0;
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__normalized_radicand = VL_RAND_RESET_Q(56);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__rad = VL_RAND_RESET_Q(56);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__next_rad = VL_RAND_RESET_Q(56);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__current_subtractend = VL_RAND_RESET_Q(56);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__next_subtractend = VL_RAND_RESET_Q(56);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__new_Q = VL_RAND_RESET_Q(56);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__running = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__start_algorithm = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT____Vcellinp__in_progress_m__set = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__start_algorithm_r = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__id_in_progress = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1 = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2 = VL_RAND_RESET_Q(64);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_hidden_bit = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_hidden_bit = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_left_shift_amt = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_left_shift_amt = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_normal = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_normal = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rm = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_inf = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_SNaN = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_QNaN = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs1_is_zero = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_inf = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_SNaN = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_QNaN = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__rs2_is_zero = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__early_terminate = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_QNaN = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_inf = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_sign[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate[__Vi0] = VL_RAND_RESET_I(13);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__special_case_results[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__clz_with_prepended_0s = VL_RAND_RESET_I(11);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__advance = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__terminate = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__divisor_r = VL_RAND_RESET_Q(55);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__new_PR = VL_RAND_RESET_Q(56);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__PR = VL_RAND_RESET_Q(56);
    VL_RAND_RESET_W(109, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__shift_count);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__advance = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz = VL_RAND_RESET_I(5);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__low_order_clz[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__sub_clz = VL_RAND_RESET_I(8);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__upper_lower[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2fp_misc_inst__DOT__fp_i2f_inst__DOT__clz_inst__DOT__clz_low_table[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__instruction = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__advance = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__id = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__done = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(84, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int_dot_frac);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_int = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_f2i_int = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__grs = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_inexact = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__f2i_frac_sticky_OR = VL_RAND_RESET_I(9);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__roundup = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smallest_signed_int_OR = VL_RAND_RESET_I(6);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__largest_unsigned_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__largest_signed_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__greater_than_largest_unsigned_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_greater_than_largest_unsigned_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__greater_than_largest_signed_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_greater_than_largest_signed_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__smaller_than_smallest_signed_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_smaller_than_smallest_signed_int = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_special = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_subtract = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_f2i_inst__DOT__r_in1 = VL_RAND_RESET_I(32);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__r_invalid_cmp = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__unordered = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__flt = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__feq = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__r_result = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__done = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__id = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_cmp_inst__DOT__sign_equ = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(69, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_r);
    VL_RAND_RESET_W(69, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__fp_class_inputs_rr);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__done = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__done_r = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__id = VL_RAND_RESET_I(3);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__wb2int_misc_inst__DOT__fp_class_inst__DOT__id_r = VL_RAND_RESET_I(3);
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_ack[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_instruction_id[__Vi0] = VL_RAND_RESET_I(12);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_done[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        for (int __Vi1=0; __Vi1<4; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rd[__Vi0][__Vi1] = VL_RAND_RESET_Q(64);
        }
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_carry[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_safe[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_hidden[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_expo_overflow[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_subnormal[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_rm[__Vi0] = VL_RAND_RESET_I(12);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        for (int __Vi1=0; __Vi1<4; ++__Vi1) {
            vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_fflags[__Vi0][__Vi1] = VL_RAND_RESET_I(5);
        }
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_clz[__Vi0] = VL_RAND_RESET_Q(44);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        VL_RAND_RESET_W(416, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_grs[__Vi0]);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_right_shift_amt[__Vi0] = VL_RAND_RESET_Q(44);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__unit_sel[__Vi0] = VL_RAND_RESET_I(2);
    }
    VL_RAND_RESET_W(209, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet);
    VL_RAND_RESET_W(209, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_packet_r);
    VL_RAND_RESET_W(141, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet);
    VL_RAND_RESET_W(141, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__round_packet_r);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_norm = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(197, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_shift = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(197, vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_pre_processing_packet_r);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__hidden_round_frac_roundup = VL_RAND_RESET_Q(54);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__advance_round = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__frac_overflow_parallel_ANDs = VL_RAND_RESET_I(9);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT____Vlvbound_he380f72e__0 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT____Vlvbound_he380f72e__0 = VL_RAND_RESET_I(1);
    vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__genblk3__BRA__0__KET____DOT__unit_done_encoder__DOT__genblk2__DOT__encoder_rom = VL_RAND_RESET_I(32);
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__unit_fflags_table[__Vi0] = VL_RAND_RESET_I(5);
    }
    for (int __Vi0=0; __Vi0<8; ++__Vi0) {
        vlSelf->taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__fp_unit_fflags_table[__Vi0] = VL_RAND_RESET_I(5);
    }
    VL_RAND_RESET_W(159, vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__reverse__30__Vfuncout);
    VL_RAND_RESET_W(159, vlSelf->__Vfunc_taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__norm_round_inst__DOT__normalize_inst__DOT__reverse__31__Vfuncout);
    vlSelf->__Vdly__taiga_sim__DOT__read_counter = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__taiga_sim__DOT__begin_read_counter = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__taiga_sim__DOT__write_counter = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__taiga_sim__DOT__begin_write_counter = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvset__taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__fpu_tracer__DOT__register_unit_id_table__v1 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__l2_to_mem__DOT__read_count = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__taiga_sim__DOT__axi_arvalid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__taiga_sim__DOT__l2_to_mem__DOT__write_burst_count = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__taiga_sim__DOT__l2_arb__DOT__burst_count = VL_RAND_RESET_I(5);
    vlSelf->__Vdlyvset__taiga_sim__DOT__l2_arb__DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__l2_arb__DOT__reserv__DOT__reservation_address__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(5);
    vlSelf->__Vdlyvset__taiga_sim__DOT__l2_arb__DOT__data_attributes_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__l2_arb__DOT__mem_data__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__inflight_count = VL_RAND_RESET_I(5);
    vlSelf->__Vdlyvset__taiga_sim__DOT__l2_arb__DOT__mem_returndata__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__l2_arb__DOT__genblk1__BRA__0__KET____DOT__input_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__l2_arb__DOT__genblk2__BRA__0__KET____DOT__input_data_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__pc_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__instruction_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__fetch_metadata_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__phys_addr_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__uses_rd_table__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__id_block__DOT__oldest_pre_issue_id = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__pc_id = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__fetch_id = VL_RAND_RESET_I(3);
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__accu_fcsr_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_float_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__is_float_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__wb2_int_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__need_int_data_table__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(3);
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__id_block__DOT__genblk1__DOT__fp_inst_id_management__DOT__fp_issued_id_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__branch_metadata_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__0__KET____DOT__tag_bank__DOT__branch_ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk1__DOT__branch_tag_banks__BRA__1__KET____DOT__tag_bank__DOT__branch_ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__0__KET____DOT__addr_table__DOT__branch_ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__bp_block__DOT__genblk2__DOT__branch_table_banks__BRA__1__KET____DOT__addr_table__DOT__branch_ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__ras_block__DOT__lut_ram__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(3);
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__ras_block__DOT__read_index_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__free_list_fifo__DOT__lut_ram__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(5);
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__free_list_fifo__DOT__lut_ram__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(5);
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__inuse_list_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_renamer_block__DOT__spec_table_ram__DOT__xilinx_gen__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__rd_to_id_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__fp_decode_and_issue_block__DOT__rd_to_id_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__register_file_block__DOT__decode_inuse_r__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__register_file_block__DOT__register_file_gen__BRA__1__KET____DOT__reg_group__DOT__register_file_bank__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__decode_inuse_r__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fp_register_file_block__DOT__register_file_gen__BRA__0__KET____DOT__reg_group__DOT__register_file_bank__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__read_index = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_index = VL_RAND_RESET_I(3);
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__lq_block__DOT__load_queue_fifo__DOT__genblk1__DOT__write_port__DOT__ram__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_attr__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_wb__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__store_data_from_issue__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_wb__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__load_store_unit_block__DOT__lsq_block__DOT__sq_block__DOT__fp_store_data_from_issue__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__gc_unit_block__DOT__state_counter = VL_RAND_RESET_I(7);
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__mulh__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__mulh__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__id__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__id__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__genblk4__DOT__mul_unit_block__DOT__valid__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__invalid_operation__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__opcode__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__id__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_special_case__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_frac__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_frac__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__possible_subnormal__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__pre_normalize_shift_amt__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_expo__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_expo__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_expo__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_sign__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_sign__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs2_sign__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_frac__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_frac__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__instruction__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__done__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_expo__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_expo__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs3_hidden_bit__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_sign__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rs1_sign__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__rm__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_QNaN__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_inf__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_zero__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__grs__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__right_shift__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__output_special_case__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__result_frac__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_special_case__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__inexact__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_QNaN__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__invalid_operation__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__id__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__zero_result_sign__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__done__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__special_case_results__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__output_inf__v3 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__expo_diff__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm__v1 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rm__v2 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__result_frac__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__subtract__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_grs_sticky_bit__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_sign__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs2_frac_aligned__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_expo_overflow__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_frac__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__rs1_grs__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__sqrt__DOT__sqrt_block__DOT__counter = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__output_special_case__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_expo_intermediate__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__result_sign__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__done__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__special_case_results__v0 = 0;
    vlSelf->__Vdly__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__div_sqrt_inst__DOT__div__DOT__fp_div_core_inst__DOT__div_mantissa_shortened__DOT__PR = VL_RAND_RESET_Q(56);
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__unit_fflags_table__v0 = 0;
    vlSelf->__Vdlyvset__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fflag_mux_inst__DOT__fp_unit_fflags_table__v0 = 0;
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__MUL__DOT__advance_stage[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        vlSelf->__Vchglast__TOP__taiga_sim__DOT__cpu__DOT__fpu_block__DOT__fpu_block__DOT__fp_madd_inst__DOT__ADD__DOT__advance_stage[__Vi0] = VL_RAND_RESET_I(1);
    }
}
