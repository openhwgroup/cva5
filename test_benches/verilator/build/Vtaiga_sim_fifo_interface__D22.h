// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_FIFO_INTERFACE__D22_H_
#define VERILATED_VTAIGA_SIM_FIFO_INTERFACE__D22_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_fifo_interface__D22 final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ pop;
    CData/*0:0*/ valid;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_fifo_interface__D22(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_fifo_interface__D22();
    VL_UNCOPYABLE(Vtaiga_sim_fifo_interface__D22);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
