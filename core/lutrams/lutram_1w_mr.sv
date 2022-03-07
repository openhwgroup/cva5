/*
 * Copyright © 2021 Eric Matthews,  Lesley Shannon
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

module lutram_1w_mr

    import cva5_config::*;

    #(
        parameter WIDTH = 32,
        parameter DEPTH = 32,
        parameter NUM_READ_PORTS = 2
    )
    (
        input logic clk,

        input logic[$clog2(DEPTH)-1:0] waddr,
        input logic[$clog2(DEPTH)-1:0] raddr [NUM_READ_PORTS],

        input logic ram_write,
        input logic[WIDTH-1:0] new_ram_data,
        output logic[WIDTH-1:0] ram_data_out [NUM_READ_PORTS]
    );

//For Xilinx with their wider selection of LUTRAMs, infer a multi-read port LUTRAM
//For Intel, build the multi-read port ram from simple-dual-port LUTRAMs
generate if (FPGA_VENDOR == XILINX) begin : xilinx_gen
    logic [WIDTH-1:0] ram [DEPTH-1:0];

    initial ram = '{default: 0};
    always_ff @ (posedge clk) begin
        if (ram_write)
            ram[waddr] <= new_ram_data;
    end

    always_comb begin
        for (int i = 0; i < NUM_READ_PORTS; i++) begin
            ram_data_out[i] = ram[raddr[i]];
        end
    end

end
else if (FPGA_VENDOR == INTEL) begin : intel_gen

    for (genvar i = 0; i < NUM_READ_PORTS; i++) begin : lutrams
        lutram_1w_1r #(.WIDTH(WIDTH), .DEPTH(DEPTH))
        write_port (
            .clk(clk),
            .waddr(waddr),
            .raddr(raddr[i]),
            .ram_write(ram_write),
            .new_ram_data(new_ram_data),
            .ram_data_out(ram_data_out[i])
        );
    end

end
endgenerate
endmodule
