// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_REGISTER_FILE_ISSUE_INTERFACE__PI1_H_
#define VERILATED_VTAIGA_SIM_REGISTER_FILE_ISSUE_INTERFACE__PI1_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_register_file_issue_interface__pi1 final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __Vdlyvset__data__v0;
    CData/*0:0*/ __Vdlyvset__data__v1;
    VlUnpacked<CData/*5:0*/, 2> phys_rs_addr;
    VlUnpacked<CData/*0:0*/, 2> rs_wb_group;
    VlUnpacked<IData/*31:0*/, 2> data;
    VlUnpacked<CData/*0:0*/, 2> inuse;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_register_file_issue_interface__pi1(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_register_file_issue_interface__pi1();
    VL_UNCOPYABLE(Vtaiga_sim_register_file_issue_interface__pi1);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
