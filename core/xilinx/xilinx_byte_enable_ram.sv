/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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
import riscv_types::*;

module xilinx_byte_enable_ram #(
        parameter LINES = 4096,
        parameter preload_file = "",
        parameter USE_PRELOAD_FILE = 0
        )
        (
        input logic clk,

        input logic[$clog2(LINES)-1:0] addr_a,
        input logic en_a,
        input logic[XLEN/8-1:0] be_a,
        input logic[XLEN-1:0] data_in_a,
        output logic[XLEN-1:0] data_out_a,

        input logic[$clog2(LINES)-1:0] addr_b,
        input logic en_b,
        input logic[XLEN/8-1:0] be_b,
        input logic[XLEN-1:0] data_in_b,
        output logic[XLEN-1:0] data_out_b
        );

    logic [31:0] ram [LINES-1:0];

    initial
    begin
        if(USE_PRELOAD_FILE)
            $readmemh(preload_file,ram, 0, LINES-1);
    end

    generate
    genvar i;
    for (i=0; i < 4; i++) begin
        always_ff @(posedge clk) begin
            if (en_a) begin
                if (be_a[i]) begin
                    ram[addr_a][8*i+:8] <= data_in_a[8*i+:8];
                    data_out_a[8*i+:8] <= data_in_a[8*i+:8];
                end else begin
                    data_out_a[8*i+:8] <= ram[addr_a][8*i+:8];
                end
            end
        end
    end
    
    for (i=0; i < 4; i++) begin
        always_ff @(posedge clk) begin
            if (en_b) begin
                if (be_b[i]) begin
                    ram[addr_b][8*i+:8] <= data_in_b[8*i+:8];
                    data_out_b[8*i+:8] <= data_in_b[8*i+:8];
                end else begin
                    data_out_b[8*i+:8] <= ram[addr_b][8*i+:8];
                end
            end
        end
    end
    endgenerate

endmodule
