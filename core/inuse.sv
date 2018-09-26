/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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

import taiga_config::*;
import taiga_types::*;

/*Overview:
 * Inuse tracking logic.  Tracks whether there is an outstanding write to any given register.
 * Inuse tracking has two write-ports.  One port, (issue), always sets bits, and (completed) always clears bits.
 */

/* Constraints
 *   + Issue has precedence over completed.  Addresses may/will overlap.
*/

/*Implementation:
 * If the addresses overlap, then issue has precedence over completed.  After a reset, all memory bits are zero.
 * Seperate memories are used for each write port (issue and completed).  Whenever a write occurs to either block,
 * the bit is toggled.  If the xor of the two memories is one, then the register is inuse.  Issues and completed occur
 * in pairs so after an instruction completes the two memories will have the same value (0 or 1).
 * If a new issue to the same address as a completing instruction occurs the memories will continue to have different values,
 * satisfing the requirement that issue has precedence over completion.
*/

module inuse (
        input logic clk,
        input logic rst,
        input logic clr,
        input logic [4:0] rs1_addr,
        input logic [4:0] rs2_addr,
        input logic [4:0] decode_rd_addr,
        input logic [4:0] wb_rd_addr,
        input logic issued,
        input logic completed,
        output logic rs1_inuse,
        output logic rs2_inuse
        );

    //Memory organized as 2 sets of dual-ported memories
    logic bankA [31:0];
    logic bankB [31:0];
    logic bankA2 [31:0];
    logic bankB2 [31:0];

    logic [4:0] w_clear;
    logic [4:0] wb_rd_addr_muxed;
    logic [4:0] decode_rd_addr_muxed;

    //////////////////////////////////////////
    //Initialize to all inuse (0,1) for simulation,
    //will be cleared by GC after reset in hardware
    // synthesis translate_off
    initial begin
        foreach(bankA[i]) begin
            bankA[i] = 0;
            bankB[i] = 1;
            bankA2[i] = 0;
            bankB2[i] = 1;
        end
    end
    // synthesis translate_on

    //After reset, clear is held for at least 32 cycles to reset memory block
    assign wb_rd_addr_muxed = clr ? w_clear : wb_rd_addr;
    assign decode_rd_addr_muxed = clr ? w_clear : decode_rd_addr;

    //reset is for simulation purposes only, not needed for actual design
    always_ff @ (posedge clk) begin
        if (rst)
            w_clear <= 0;
        else
            w_clear <= w_clear + clr;
    end

    always_ff @ (posedge clk) begin
            bankA[decode_rd_addr_muxed] <= clr | (issued ^ bankA[decode_rd_addr_muxed]);
            bankA2[decode_rd_addr_muxed] <= clr | (issued ^ bankA2[decode_rd_addr_muxed]);
    end

    always_ff @ (posedge clk) begin
            bankB[wb_rd_addr_muxed] <= clr | (completed ^ bankB[wb_rd_addr_muxed]);
            bankB2[wb_rd_addr_muxed] <= clr | (completed ^ bankB2[wb_rd_addr_muxed]);
    end

    assign rs1_inuse = bankA[rs1_addr] ^ bankB[rs1_addr];
    assign rs2_inuse = bankB2[rs2_addr] ^ bankA2[rs2_addr];

    ////////////////////////////////////////////////////
    //Assertions


    ////////////////////////////////////////////////////
    //Simulation Only
    // synthesis translate_off
    logic sim_inuse [31:0];
    always_comb begin
        foreach (sim_inuse[i])
            sim_inuse[i] = bankA[i] ^ bankB[i];
    end
    // synthesis translate_on

endmodule


