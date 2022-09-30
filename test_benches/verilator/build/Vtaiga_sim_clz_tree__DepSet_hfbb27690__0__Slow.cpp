// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim_clz_tree.h"

VL_ATTR_COLD void Vtaiga_sim_clz_tree___ctor_var_reset(Vtaiga_sim_clz_tree* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtaiga_sim__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+                  Vtaiga_sim_clz_tree___ctor_var_reset\n"); );
    // Body
    vlSelf->clz_input = VL_RAND_RESET_Q(64);
    vlSelf->clz = VL_RAND_RESET_I(6);
    vlSelf->__PVT__encoded_input = VL_RAND_RESET_Q(64);
    vlSelf->__PVT__clz_plus1 = VL_RAND_RESET_I(7);
    vlSelf->__PVT__compressed_3bit_vector = VL_RAND_RESET_Q(48);
    vlSelf->__PVT__compressed_4bit_vector = VL_RAND_RESET_I(32);
    vlSelf->__Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2 = VL_RAND_RESET_I(3);
    vlSelf->__Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2 = VL_RAND_RESET_I(4);
    vlSelf->__Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2 = VL_RAND_RESET_I(4);
    vlSelf->__Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2 = VL_RAND_RESET_I(4);
    vlSelf->__Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2 = VL_RAND_RESET_I(4);
    vlSelf->__Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2 = VL_RAND_RESET_I(4);
    vlSelf->__Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2 = VL_RAND_RESET_I(4);
    vlSelf->__Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2 = VL_RAND_RESET_I(4);
    vlSelf->__Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2 = VL_RAND_RESET_I(4);
    vlSelf->__Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2 = VL_RAND_RESET_I(5);
    vlSelf->__Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2 = VL_RAND_RESET_I(5);
    vlSelf->__Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2 = VL_RAND_RESET_I(5);
    vlSelf->__Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2 = VL_RAND_RESET_I(5);
    vlSelf->__Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2 = VL_RAND_RESET_I(6);
    vlSelf->__Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2 = VL_RAND_RESET_I(6);
}
