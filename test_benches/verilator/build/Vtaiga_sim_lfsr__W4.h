// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtaiga_sim.h for the primary calling header

#ifndef VERILATED_VTAIGA_SIM_LFSR__W4_H_
#define VERILATED_VTAIGA_SIM_LFSR__W4_H_  // guard

#include "verilated.h"

class Vtaiga_sim__Syms;

class Vtaiga_sim_lfsr__W4 final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    VL_IN8(clk,0,0);
    VL_IN8(rst,0,0);
    VL_IN8(en,0,0);
    VL_OUT8(value,3,0);
    CData/*1:0*/ __PVT__feedback_input;
    CData/*0:0*/ __PVT__feedback;

    // INTERNAL VARIABLES
    Vtaiga_sim__Syms* const vlSymsp;

    // PARAMETERS
    static constexpr VlUnpacked<VlUnpacked<IData/*31:0*/, 5>, 14> __PVT__TAPS = {{
        {{
            0x00000002U, 0x00000003U, 0x00000002U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000004U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000005U, 0x00000003U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000006U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x00000007U, 0x00000006U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000008U, 0x00000006U, 0x00000005U,
            0x00000004U
        }},
        {{
            0x00000002U, 0x00000009U, 0x00000005U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000aU, 0x00000007U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000002U, 0x0000000bU, 0x00000009U, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x0000000cU, 0x00000006U, 0x00000004U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000dU, 0x00000004U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000004U, 0x0000000eU, 0x00000005U, 0x00000003U,
            0x00000001U
        }},
        {{
            0x00000002U, 0x0000000fU, 0x0000000eU, 0x00000000U,
            0x00000000U
        }},
        {{
            0x00000004U, 0x00000010U, 0x0000000fU, 0x0000000dU,
            0x00000004U
        }}
    }};

    // CONSTRUCTORS
    Vtaiga_sim_lfsr__W4(Vtaiga_sim__Syms* symsp, const char* name);
    ~Vtaiga_sim_lfsr__W4();
    VL_UNCOPYABLE(Vtaiga_sim_lfsr__W4);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);


#endif  // guard
