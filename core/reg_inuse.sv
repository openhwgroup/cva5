/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */

import cva5_config::*;
import cva5_types::*;

module reg_inuse (
        input logic clk,
        input logic rst,
        input logic clr,
        input logic [4:0] rs1_addr,
        input logic [4:0] rs2_addr,
        input logic [4:0] issued_rd_addr,
        input logic [4:0] retired_rd_addr,
        input logic issued,
        input logic retired,
        output logic rs1_inuse,
        output logic rs2_inuse
        );
    ////////////////////////////////////////////////////
    //Memory organized as 2 sets of dual-ported memories
    logic bankA [32];
    logic bankB [32];

    logic [4:0] w_clear;
    logic [4:0] wb_rd_addr_muxed;

    logic wb_collision;
    ////////////////////////////////////////////////////
    //Implementation

    //////////////////////////////////////////
    //Initialize to all inuse (0,1) for simulation,
    //will be cleared by GC after reset in hardware
    // synthesis translate_off
    initial bankA = '{default: 0};
    initial bankB = '{default: 0};
    // synthesis translate_on

    //After reset, clear is held for at least 32 cycles to reset memory block
    assign wb_rd_addr_muxed = clr ? w_clear : retired_rd_addr;


    //reset is for simulation purposes only, not needed for actual design
    always_ff @ (posedge clk) begin
        if (rst)
            w_clear <= 0;
        else
            w_clear <= w_clear + 5'(clr);
    end

    assign wb_collision = retired && (issued_rd_addr == retired_rd_addr);

    always_ff @ (posedge clk) begin
        if (issued)
            bankA[issued_rd_addr] <= wb_collision ? ~bankA[wb_rd_addr_muxed] : ~bankB[issued_rd_addr];
    end

    always_ff @ (posedge clk) begin
        if (retired | clr)
            bankB[wb_rd_addr_muxed] <= bankA[wb_rd_addr_muxed];
    end

    assign rs1_inuse = bankA[rs1_addr] ^ bankB[rs1_addr];
    assign rs2_inuse = bankA[rs2_addr] ^ bankB[rs2_addr];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Simulation Only
    // synthesis translate_off
    logic sim_inuse [32];
    always_comb begin
        foreach (sim_inuse[i])
            sim_inuse[i] = bankA[i] ^ bankB[i];
    end
    // synthesis translate_on


endmodule




