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
 
module one_hot_to_integer
        #(
        parameter C_WIDTH = 32
        )
        (
        input logic [C_WIDTH-1:0] one_hot,
        output logic [$clog2(C_WIDTH)-1:0] int_out
        );

    always_comb begin
        int_out = 0;
        for (int i=1; i < C_WIDTH; i=i+1)
            if (one_hot[i]) int_out = i;
    end

endmodule
