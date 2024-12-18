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

module tdp_ram

    #(
        parameter ADDR_WIDTH = 10,
        parameter NUM_COL = 4, //Number of independently writeable components
        parameter COL_WIDTH = 16, //Width the "byte" enable controls
        parameter PIPELINE_DEPTH = 1, //Depth of the output pipeline, is latency in clock cycles
        parameter CASCADE_DEPTH = 4, //Maximum depth of the memory block cascade
        parameter USE_PRELOAD = 0,
        parameter PRELOAD_FILE = ""
    )
    (
        input logic clk,
        //Port A
        input logic a_en,
        input logic[NUM_COL-1:0] a_wbe,
        input logic[COL_WIDTH*NUM_COL-1:0] a_wdata,
        input logic[ADDR_WIDTH-1:0] a_addr,
        output logic[COL_WIDTH*NUM_COL-1:0] a_rdata,

        //Port B
        input logic b_en,
        input logic[NUM_COL-1:0] b_wbe,
        input logic[COL_WIDTH*NUM_COL-1:0] b_wdata,
        input logic[ADDR_WIDTH-1:0] b_addr,
        output logic[COL_WIDTH*NUM_COL-1:0] b_rdata
    );

    localparam DATA_WIDTH = COL_WIDTH*NUM_COL;

    (* cascade_height = CASCADE_DEPTH, ramstyle = "no_rw_check" *) //Higher depths use less resources but are slower
    logic[DATA_WIDTH-1:0] mem[(1<<ADDR_WIDTH)-1:0]; 

    initial begin
        if (USE_PRELOAD)
            $readmemh(PRELOAD_FILE, mem, 0);
    end

    //A read/write
    logic[DATA_WIDTH-1:0] a_ram_output;
    always_ff @(posedge clk) begin
        if (a_en) begin
            for (int i = 0; i < NUM_COL; i++) begin
                if (a_wbe[i])
                    mem[a_addr][i*COL_WIDTH +: COL_WIDTH] <= a_wdata[i*COL_WIDTH +: COL_WIDTH];
            end
            if (~|a_wbe)
                a_ram_output <= mem[a_addr];
        end
    end

    //A pipeline
    generate if (PIPELINE_DEPTH > 0) begin : gen_a_pipeline
        logic[DATA_WIDTH-1:0] a_data_pipeline[PIPELINE_DEPTH-1:0];
        logic[PIPELINE_DEPTH-1:0] a_en_pipeline;
        
        always_ff @(posedge clk) begin
            for (int i = 0; i < PIPELINE_DEPTH; i++) begin
                a_en_pipeline[i] <= i == 0 ? a_en : a_en_pipeline[i-1];
                if (a_en_pipeline[i])
                    a_data_pipeline[i] <= i == 0 ? a_ram_output : a_data_pipeline[i-1];
            end
        end
        assign a_rdata = a_data_pipeline[PIPELINE_DEPTH-1];
    end
    else begin : gen_a_transparent_output
        assign a_rdata = a_ram_output;
    end endgenerate


    //B read/write
    logic[DATA_WIDTH-1:0] b_ram_output;
    always_ff @(posedge clk) begin
        if (b_en) begin
            for (int i = 0; i < NUM_COL; i++) begin
                if (b_wbe[i])
                    mem[b_addr][i*COL_WIDTH +: COL_WIDTH] <= b_wdata[i*COL_WIDTH +: COL_WIDTH];
            end
            if (~|b_wbe)
                b_ram_output <= mem[b_addr];
        end
    end

    //B pipeline
    generate if (PIPELINE_DEPTH > 0) begin : gen_b_pipeline
        logic[DATA_WIDTH-1:0] b_data_pipeline[PIPELINE_DEPTH-1:0];
        logic[PIPELINE_DEPTH-1:0] b_en_pipeline;
        
        always_ff @(posedge clk) begin
            for (int i = 0; i < PIPELINE_DEPTH; i++) begin
                b_en_pipeline[i] <= i == 0 ? b_en : b_en_pipeline[i-1];
                if (b_en_pipeline[i])
                    b_data_pipeline[i] <= i == 0 ? b_ram_output : b_data_pipeline[i-1];
            end
        end
        assign b_rdata = b_data_pipeline[PIPELINE_DEPTH-1];
    end
    else begin : gen_b_transparent_output
        assign b_rdata = b_ram_output;
    end endgenerate

endmodule
