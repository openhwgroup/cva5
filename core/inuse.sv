/*
 * Copyright © 2018-2019 Eric Matthews,  Lesley Shannon
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

    logic [4:0] w_clear;
    logic [4:0] wb_rd_addr_muxed;
    logic [4:0] decode_rd_addr_muxed;

    logic wb_collision;
    logic rd_inuse;
    //////////////////////////////////////////
    //Initialize to all inuse (0,1) for simulation,
    //will be cleared by GC after reset in hardware
    // synthesis translate_off
    initial begin
        foreach(bankA[i]) begin
            bankA[i] = 0;
            bankB[i] = 1;
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
            w_clear <= w_clear + 5'(clr);
    end

    //Toggle issue (bankA) and write-back (bankB) values for inuse tracking
    //Special cases are when multiple instructions are in flight that write to the same address
    //Only the newest write will toggle BankB
    //When issueing multiple times, don't toggle for subsequent issues unless the previous write is completing on this cycle
	assign wb_collision = completed && (decode_rd_addr == wb_rd_addr);
	assign rd_inuse = ~wb_collision & (bankA[decode_rd_addr_muxed] ^ bankB[decode_rd_addr_muxed]);

    always_ff @ (posedge clk) begin
        	bankA[decode_rd_addr_muxed] <= clr | ((~rd_inuse & issued) ^ bankA[decode_rd_addr_muxed]);
    end

    always_ff @ (posedge clk) begin
        	bankB[wb_rd_addr_muxed] <= clr | (completed ^ bankB[wb_rd_addr_muxed]);
    end

    assign rs1_inuse = bankA[rs1_addr] ^ bankB[rs1_addr];
    assign rs2_inuse = bankA[rs2_addr] ^ bankB[rs2_addr];

    ////////////////////////////////////////////////////
    //Assertions


    ////////////////////////////////////////////////////
    //Simulation Only
    // synthesis translate_off
    logic sim_inuse [31:0];
    always_comb begin
        foreach (sim_inuse[i])
            sim_inuse[i] = bankA[i] ~^ bankB[i];
    end
    // synthesis translate_on

endmodule



