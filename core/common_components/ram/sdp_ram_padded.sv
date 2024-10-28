/*
 * Copyright © 2024 Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module sdp_ram_padded

    #(
        parameter ADDR_WIDTH = 10,
        parameter NUM_COL = 4, //Number of independently writeable components
        parameter COL_WIDTH = 16, //Width the "byte" enable controls
        parameter PIPELINE_DEPTH = 1, //Depth of the output pipeline, is latency in clock cycles
        parameter CASCADE_DEPTH = 4 //Maximum depth of the memory block cascade
    )
    (
        input logic clk,
        //Port A
        input logic a_en,
        input logic[NUM_COL-1:0] a_wbe,
        input logic[COL_WIDTH*NUM_COL-1:0] a_wdata,
        input logic[ADDR_WIDTH-1:0] a_addr,

        //Port B
        input logic b_en,
        input logic[ADDR_WIDTH-1:0] b_addr,
        output logic[COL_WIDTH*NUM_COL-1:0] b_rdata
    );

    localparam DATA_WIDTH = COL_WIDTH*NUM_COL;

    //Pad columns to the nearest multiple of 8 or 9 to allow the use of the byte enable
    //This results in a more compact BRAM encoding
    localparam PAD_WIDTH8 = (8 - (COL_WIDTH % 8)) % 8;
    localparam PAD_WIDTH9 = (9 - (COL_WIDTH % 9)) % 9;
    localparam PAD_WIDTH = PAD_WIDTH8 <= PAD_WIDTH9 ? PAD_WIDTH8 : PAD_WIDTH9;
    localparam PADDED_WIDTH = COL_WIDTH + PAD_WIDTH;
    localparam TOTAL_WIDTH = NUM_COL * PADDED_WIDTH;

    generate if (PAD_WIDTH == 0 || NUM_COL == 1) begin : gen_no_padding
        sdp_ram #(
            .ADDR_WIDTH(ADDR_WIDTH),
            .NUM_COL(NUM_COL),
            .COL_WIDTH(COL_WIDTH),
            .PIPELINE_DEPTH(PIPELINE_DEPTH),
            .CASCADE_DEPTH(CASCADE_DEPTH)
        ) mem (.*);
    end else begin : gen_padded
        logic[TOTAL_WIDTH-1:0] a_padded;
        logic[TOTAL_WIDTH-1:0] b_padded;

        always_comb begin
            a_padded = 'x;
            for (int i = 0; i < NUM_COL; i++) begin
                a_padded[i*PADDED_WIDTH+:COL_WIDTH] = a_wdata[i*COL_WIDTH+:COL_WIDTH];
                b_rdata[i*COL_WIDTH+:COL_WIDTH] = b_padded[i*PADDED_WIDTH+:COL_WIDTH];
            end
        end

        sdp_ram #(
            .ADDR_WIDTH(ADDR_WIDTH),
            .NUM_COL(NUM_COL),
            .COL_WIDTH(PADDED_WIDTH),
            .PIPELINE_DEPTH(PIPELINE_DEPTH),
            .CASCADE_DEPTH(CASCADE_DEPTH)
        ) mem (
            .a_wdata(a_padded),
            .b_rdata(b_padded),
        .*);
    end endgenerate

endmodule
