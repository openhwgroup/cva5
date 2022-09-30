// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_UNSIGNED_SQRT_INTERFACE__D38_H_
#define VERILATED_VTAIGA_SIM_UNSIGNED_SQRT_INTERFACE__D38_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_unsigned_sqrt_interface__D38 final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ done;
    QData/*55:0*/ radicand;
    QData/*55:0*/ remainder;
    QData/*55:0*/ quotient;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_unsigned_sqrt_interface__D38(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_unsigned_sqrt_interface__D38();
    VL_UNCOPYABLE(Vtaiga_sim_unsigned_sqrt_interface__D38);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
