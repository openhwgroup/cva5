/*
 * Copyright © 2023 Eric Matthews,  Lesley Shannon
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



module dual_port_bram

    import cva5_config::*;
    import cva5_types::*;
    import riscv_types::*;

	#(
        parameter WIDTH = 32,
        parameter LINES = 4096
    )
    (
        input logic clk,

        input logic en_a,
        input logic wen_a,
        input logic[$clog2(LINES)-1:0] addr_a,
        input logic[WIDTH-1:0] data_in_a,
        output logic[WIDTH-1:0] data_out_a,

        input logic en_b,
        input logic wen_b,
        input logic[$clog2(LINES)-1:0] addr_b,
        input logic[WIDTH-1:0] data_in_b,
        output logic[WIDTH-1:0] data_out_b
    );

    (* ram_style = "block", ramstyle = "no_rw_check" *) logic [WIDTH-1:0] ram [LINES];
    initial ram = '{default: 0};

    always_ff @ (posedge clk) begin
        if (en_a) begin
            if (wen_a)
                ram[addr_a] <= data_in_a;
            data_out_a <= ram[addr_a];
        end
    end

    always_ff @ (posedge clk) begin
        if (en_b) begin
            if (wen_b)
                ram[addr_b] <= data_in_b;
            data_out_b <= ram[addr_b];
        end
    end

endmodule
