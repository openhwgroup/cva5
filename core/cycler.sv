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
 

module  cycler
        #(
        parameter C_WIDTH = 2
        )
        (
        input logic clk,
        input logic rst,
        input logic en,
        output logic [C_WIDTH - 1: 0] one_hot
        );

    generate
        if (C_WIDTH == 1) begin
            assign one_hot = 1'b1;
        end
        else begin
            always_ff @ (posedge clk) begin
                if (rst) begin
                    one_hot[C_WIDTH-1:1] <= '0;
                    one_hot[0] <= 1'b1;
                end
                else if (en) begin
                    one_hot[C_WIDTH-1:1] <= one_hot[C_WIDTH-2:0];
                    one_hot[0] <= one_hot[C_WIDTH-1];
                end
            end
        end
    endgenerate

endmodule
