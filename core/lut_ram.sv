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

module lut_ram #(
        parameter WIDTH = 32,
        parameter DEPTH = 32,
        parameter READ_PORTS = 2
        )
        (
        input logic clk,

        input logic[$clog2(DEPTH)-1:0] waddr,
        input logic[$clog2(DEPTH)-1:0] raddr [READ_PORTS],

        input logic ram_write,
        input logic[WIDTH-1:0] new_ram_data,
        output logic[WIDTH-1:0] ram_data_out [READ_PORTS]

        );

    (* ramstyle = "MLAB, no_rw_check" *) logic [WIDTH-1:0] ram [DEPTH-1:0];

    initial ram = '{default: 0};
    always_ff @ (posedge clk) begin
        if (ram_write)
            ram[waddr] <= new_ram_data;
    end

    always_comb begin
        for (int i = 0; i < READ_PORTS; i++) begin
            ram_data_out[i] = ram[raddr[i]];
        end
    end

endmodule
