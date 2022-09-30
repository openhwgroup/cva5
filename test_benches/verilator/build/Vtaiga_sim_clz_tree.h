// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_CLZ_TREE_H_
#define VERILATED_VTAIGA_SIM_CLZ_TREE_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_clz_tree final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    VL_OUT8(clz,5,0);
    CData/*6:0*/ __PVT__clz_plus1;
    CData/*2:0*/ __Vcellout__genblk2__BRA__0__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__1__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__2__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__3__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__4__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__5__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__6__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__7__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__8__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__9__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__10__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__11__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__12__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__13__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__14__KET____DOT__merge_2to3____pinNumber2;
    CData/*2:0*/ __Vcellout__genblk2__BRA__15__KET____DOT__merge_2to3____pinNumber2;
    CData/*3:0*/ __Vcellout__genblk3__BRA__0__KET____DOT__merge_3to4____pinNumber2;
    CData/*3:0*/ __Vcellout__genblk3__BRA__1__KET____DOT__merge_3to4____pinNumber2;
    CData/*3:0*/ __Vcellout__genblk3__BRA__2__KET____DOT__merge_3to4____pinNumber2;
    CData/*3:0*/ __Vcellout__genblk3__BRA__3__KET____DOT__merge_3to4____pinNumber2;
    CData/*3:0*/ __Vcellout__genblk3__BRA__4__KET____DOT__merge_3to4____pinNumber2;
    CData/*3:0*/ __Vcellout__genblk3__BRA__5__KET____DOT__merge_3to4____pinNumber2;
    CData/*3:0*/ __Vcellout__genblk3__BRA__6__KET____DOT__merge_3to4____pinNumber2;
    CData/*3:0*/ __Vcellout__genblk3__BRA__7__KET____DOT__merge_3to4____pinNumber2;
    CData/*4:0*/ __Vcellout__genblk4__BRA__0__KET____DOT__merge_4to5____pinNumber2;
    CData/*4:0*/ __Vcellout__genblk4__BRA__1__KET____DOT__merge_4to5____pinNumber2;
    CData/*4:0*/ __Vcellout__genblk4__BRA__2__KET____DOT__merge_4to5____pinNumber2;
    CData/*4:0*/ __Vcellout__genblk4__BRA__3__KET____DOT__merge_4to5____pinNumber2;
    CData/*5:0*/ __Vcellout__genblk5__BRA__0__KET____DOT__merge_5to6____pinNumber2;
    CData/*5:0*/ __Vcellout__genblk5__BRA__1__KET____DOT__merge_5to6____pinNumber2;
    IData/*31:0*/ __PVT__compressed_4bit_vector;
    VL_IN64(clz_input,63,0);
    QData/*63:0*/ __PVT__encoded_input;
    QData/*47:0*/ __PVT__compressed_3bit_vector;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_clz_tree(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_clz_tree();
    VL_UNCOPYABLE(Vtaiga_sim_clz_tree);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
