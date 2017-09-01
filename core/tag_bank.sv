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

module tag_bank  #(
        parameter WIDTH = 32,
        parameter LINES = 512
        )
        (

        input logic clk,
        input logic rst,

        input logic[$clog2(LINES)-1:0] addr_a,
        input logic[$clog2(LINES)-1:0] addr_b,
        input logic en_a,
        input logic en_b,
        input logic wen_a,
        input logic wen_b,
        input logic [WIDTH-1:0] data_in_a,
        input logic [WIDTH-1:0] data_in_b,
        output logic [WIDTH-1:0] data_out_a,
        output logic [WIDTH-1:0] data_out_b
        );

    (* ramstyle = "no_rw_check" *) logic  [WIDTH-1:0] tag_entry [LINES-1:0];

    integer i;
    initial for (i=0; i<LINES; i=i+1) tag_entry[i] = 0;

    always_ff @ (posedge clk) begin
        if (en_a) begin
            if (wen_a)
                tag_entry[addr_a] <= data_in_a;
            else
                data_out_a <= tag_entry[addr_a];
        end
    end

    always_ff @ (posedge clk) begin
        if (en_b) begin
            if (wen_b) begin
                tag_entry[addr_b] <= data_in_b;
            end
            else begin
                data_out_b <= tag_entry[addr_b];
            end
        end
    end



endmodule
