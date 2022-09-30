// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_LS_SUB_UNIT_INTERFACE__PI11_H_
#define VERILATED_VTAIGA_SIM_LS_SUB_UNIT_INTERFACE__PI11_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_ls_sub_unit_interface__pi11 final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ data_valid;
    CData/*0:0*/ new_request;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_ls_sub_unit_interface__pi11(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_ls_sub_unit_interface__pi11();
    VL_UNCOPYABLE(Vtaiga_sim_ls_sub_unit_interface__pi11);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
