// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_FP_REGISTER_FILE_ISSUE_INTERFACE_H_
#define VERILATED_VTAIGA_SIM_FP_REGISTER_FILE_ISSUE_INTERFACE_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_fp_register_file_issue_interface final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __Vdlyvset__data__v0;
    CData/*0:0*/ __Vdlyvset__data__v1;
    CData/*0:0*/ __Vdlyvset__data__v2;
    VlUnpacked<CData/*5:0*/, 3> phys_rs_addr;
    VlUnpacked<CData/*0:0*/, 3> rs_wb_group;
    VlUnpacked<QData/*63:0*/, 3> data;
    VlUnpacked<CData/*0:0*/, 3> inuse;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_fp_register_file_issue_interface(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_fp_register_file_issue_interface();
    VL_UNCOPYABLE(Vtaiga_sim_fp_register_file_issue_interface);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
