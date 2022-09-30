// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtaiga_sim.h for the primary calling header

#include "verilated.h"

#include "Vtaiga_sim__Syms.h"
#include "Vtaiga_sim_fifo_interface__Db0.h"

void Vtaiga_sim_fifo_interface__Db0___ctor_var_reset(Vtaiga_sim_fifo_interface__Db0* vlSelf);

Vtaiga_sim_fifo_interface__Db0::Vtaiga_sim_fifo_interface__Db0(Vtaiga_sim__Syms* symsp, const char* name)
    : VerilatedModule{name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtaiga_sim_fifo_interface__Db0___ctor_var_reset(this);
}

void Vtaiga_sim_fifo_interface__Db0::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

Vtaiga_sim_fifo_interface__Db0::~Vtaiga_sim_fifo_interface__Db0() {
}
