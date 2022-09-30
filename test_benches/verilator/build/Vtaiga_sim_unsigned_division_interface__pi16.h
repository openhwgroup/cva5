// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_UNSIGNED_DIVISION_INTERFACE__PI16_H_
#define VERILATED_VTAIGA_SIM_UNSIGNED_DIVISION_INTERFACE__PI16_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_unsigned_division_interface__pi16 final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ start;
    CData/*0:0*/ done;
    CData/*0:0*/ __Vdly__done;
    QData/*54:0*/ quotient;
    QData/*54:0*/ __Vdly__quotient;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_unsigned_division_interface__pi16(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_unsigned_division_interface__pi16();
    VL_UNCOPYABLE(Vtaiga_sim_unsigned_division_interface__pi16);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
