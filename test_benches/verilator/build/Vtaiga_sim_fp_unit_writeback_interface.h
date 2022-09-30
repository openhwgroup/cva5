// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_FP_UNIT_WRITEBACK_INTERFACE_H_
#define VERILATED_VTAIGA_SIM_FP_UNIT_WRITEBACK_INTERFACE_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_fp_unit_writeback_interface final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ ack;
    CData/*2:0*/ id;
    CData/*0:0*/ done;
    CData/*0:0*/ expo_overflow;
    CData/*4:0*/ fflags;
    CData/*2:0*/ rm;
    CData/*0:0*/ carry;
    CData/*0:0*/ safe;
    CData/*0:0*/ hidden;
    CData/*0:0*/ right_shift;
    CData/*0:0*/ subnormal;
    SData/*10:0*/ clz;
    SData/*10:0*/ right_shift_amt;
    VlWide<4>/*103:0*/ grs;
    QData/*63:0*/ rd;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vtaiga_sim_fp_unit_writeback_interface(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_fp_unit_writeback_interface();
    VL_UNCOPYABLE(Vtaiga_sim_fp_unit_writeback_interface);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
