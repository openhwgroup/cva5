// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_L2_ARBITRATION_INTERFACE_H_
#define VERILATED_VTAIGA_SIM_L2_ARBITRATION_INTERFACE_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_l2_arbitration_interface final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*1:0*/ requests;
    CData/*0:0*/ grantee_i;
    CData/*1:0*/ grantee_v;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_l2_arbitration_interface(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_l2_arbitration_interface();
    VL_UNCOPYABLE(Vtaiga_sim_l2_arbitration_interface);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
