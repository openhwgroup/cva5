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



module intel_byte_enable_ram 

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    #(
        parameter LINES = 8192,
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

    (* ramstyle = "no_rw_check" *) logic [3:0][7:0] ram [LINES-1:0];

    initial
    begin
        if(USE_PRELOAD_FILE)
            $readmemh(preload_file,ram, 0, LINES-1);
    end


    always_ff @(posedge clk) begin
        if (en_a) begin
            if (be_a[0]) ram[addr_a][0] <= data_in_a[7:0];
            if (be_a[1]) ram[addr_a][1] <= data_in_a[15:8];
            if (be_a[2]) ram[addr_a][2] <= data_in_a[23:16];
            if (be_a[3]) ram[addr_a][3] <= data_in_a[31:24];
        end
        data_out_a <= ram[addr_a];
    end


    always_ff @(posedge clk) begin
        if (en_b) begin
            if (be_b[0]) ram[addr_b][0] <= data_in_b[7:0];
            if (be_b[1]) ram[addr_b][1] <= data_in_b[15:8];
            if (be_b[2]) ram[addr_b][2] <= data_in_b[23:16];
            if (be_b[3]) ram[addr_b][3] <= data_in_b[31:24];
        end
        data_out_b <= ram[addr_b];
    end


endmodule
