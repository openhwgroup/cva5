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
 
import taiga_config::*;
import taiga_types::*;

module altera_byte_enable_ram #(
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
