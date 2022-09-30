// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_AXI_INTERFACE_H_
#define VERILATED_VTAIGA_SIM_AXI_INTERFACE_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_axi_interface final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ arready;
    CData/*0:0*/ rvalid;
    CData/*0:0*/ awready;
    CData/*0:0*/ wready;
    CData/*0:0*/ bvalid;
    CData/*0:0*/ __Vdly__rvalid;
    CData/*0:0*/ __Vdly__arready;
    CData/*0:0*/ __Vdly__wready;
    CData/*0:0*/ __Vdly__awready;
    IData/*31:0*/ rdata;
    IData/*31:0*/ awaddr;
    IData/*31:0*/ wdata;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_axi_interface(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_axi_interface();
    VL_UNCOPYABLE(Vtaiga_sim_axi_interface);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
