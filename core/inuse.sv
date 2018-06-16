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

//Inuse tracking stored in a 2-write port 2-read port memory implemented with multiple 1r/1w port memories and xor
//issue sets bits, retired instructions clear, and issue takes precedence over retiring
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

    logic bankA [31:0];
    logic bankB [31:0];

    logic [4:0] w_clear;
    logic [4:0] wb_rd_addr_muxed;

    logic write_collision;

    //////////////////////////////////////////
    //Initialize to zero
    initial begin
        foreach(bankA[i]) begin
            bankA[i] = 0;
            bankB[i] = 0;
        end
    end

    assign write_collision = issued && (decode_rd_addr == wb_rd_addr);

    //After reset, clear is held for at least 32 cycles to reset memory block
    assign wb_rd_addr_muxed = clr ? w_clear : wb_rd_addr;
    always_ff @ (posedge clk) begin
        if (rst)
            w_clear <= 0;
        else if (clr)
            w_clear <= w_clear + 1;
    end

    always_ff @ (posedge clk) begin
        if (issued)
            bankA[decode_rd_addr] <= (1 ^ bankB[decode_rd_addr]);
    end
    always_ff @ (posedge clk) begin
        if ((completed & ~write_collision) | clr)
            bankB[wb_rd_addr_muxed] <= 0 ^ bankA[wb_rd_addr_muxed];
    end

    assign rs1_inuse = bankA[rs1_addr] ^ bankB[rs1_addr];
    assign rs2_inuse = bankB[rs2_addr] ^ bankA[rs2_addr];

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(clr & issued)) else $error("Write ocured to inuse memory during clear operation!");
    end

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


