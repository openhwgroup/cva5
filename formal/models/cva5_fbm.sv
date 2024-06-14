//
// Copyright © 2020  Stuart Hoad, Lesley Shannon
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Initial code developed under the supervision of Dr. Lesley Shannon,
// Reconfigurable Computing Lab, Simon Fraser University.
//
// Author(s):
//             Stuart Hoad <shoad@sfu.ca>
//
// CVA5 Formal Behavioural Model

//****************************************************************************
//****************************************************************************


import cva5_config::*;
import riscv_types::*;
import cva5_types::*;

module cva5_fbm (
        input logic clk,
        input logic rst,

        local_memory_interface.formal instruction_bram,
        local_memory_interface.formal data_bram,

        axi_interface.formal m_axi,
        avalon_interface.formal m_avalon,
        wishbone_interface.formal m_wishbone,

        input trace_outputs_t tr,

        l2_requester_interface.formal l2,

        input logic timer_interrupt,
        input logic interrupt
        );

//****************************************************************************
// Interface properties
//****************************************************************************

    // AXI constraints.
    // CVA5 does not deal with bad AXI responses, so need to constrain to avoid them
    // REVISIT add AXI protocol properties
    axi4_basic_props
    u_ppb_axi (
        .clk 		        (clk),
        .rst 		        (rst),
        .axi_if		        (m_axi)
    );


endmodule
