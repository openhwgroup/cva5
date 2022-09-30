// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_L2_REQUESTER_INTERFACE_H_
#define VERILATED_VTAIGA_SIM_L2_REQUESTER_INTERFACE_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_l2_requester_interface final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*3:0*/ be;
    CData/*0:0*/ rnw;
    CData/*0:0*/ is_amo;
    CData/*4:0*/ amo_type_or_burst_size;
    CData/*1:0*/ sub_id;
    CData/*0:0*/ request_push;
    CData/*0:0*/ inv_ack;
    CData/*0:0*/ wr_data_push;
    CData/*0:0*/ rd_data_ack;
    IData/*29:0*/ addr;
    IData/*31:0*/ wr_data;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_l2_requester_interface(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_l2_requester_interface();
    VL_UNCOPYABLE(Vtaiga_sim_l2_requester_interface);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
