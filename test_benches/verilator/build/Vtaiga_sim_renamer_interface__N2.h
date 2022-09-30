// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_RENAMER_INTERFACE__N2_H_
#define VERILATED_VTAIGA_SIM_RENAMER_INTERFACE__N2_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_renamer_interface__N2 final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    SData/*11:0*/ phys_rs_addr;
    CData/*5:0*/ phys_rd_addr;
    CData/*1:0*/ rs_wb_group;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_renamer_interface__N2(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_renamer_interface__N2();
    VL_UNCOPYABLE(Vtaiga_sim_renamer_interface__N2);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
