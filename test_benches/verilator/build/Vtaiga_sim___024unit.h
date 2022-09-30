// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM___024UNIT_H_
#define VERILATED_VTAIGA_SIM___024UNIT_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim___024unit final : public VerilatedModule {
  public:

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim___024unit(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim___024unit();
    VL_UNCOPYABLE(Vtaiga_sim___024unit);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
