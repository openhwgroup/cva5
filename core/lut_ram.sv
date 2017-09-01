/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */
 
module lut_ram #(
        parameter WIDTH = 32,
        parameter DEPTH = 32
        )
        (
        input logic clk,

        input logic[$clog2(DEPTH)-1:0] waddr,
        input logic[$clog2(DEPTH)-1:0] raddr,

        input logic ram_write,
        input logic[WIDTH-1:0] new_ram_data,
        output logic[WIDTH-1:0] ram_data_out

        );

    (* ramstyle = "MLAB, no_rw_check" *) logic [WIDTH-1:0] ram [DEPTH-1:0];

    initial begin
        for (integer i=0; i<DEPTH; i=i+1) begin
            ram[i] = '0;
        end
    end

    always_ff @ (posedge clk) begin
        if (ram_write)
            ram[waddr] <= new_ram_data;
    end

    assign ram_data_out = ram[raddr];

endmodule
