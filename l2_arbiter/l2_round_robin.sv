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
 
import l2_config_and_types::*;

module l2_round_robin
        (
        input logic clk,
        input logic rst,
        l2_arbitration_interface.arbiter arb
        );

    logic [$clog2(L2_NUM_PORTS)-1:0] state;
    logic[$clog2(L2_NUM_PORTS)-1:0] muxes [L2_NUM_PORTS-1:0];

    generate if(L2_NUM_PORTS == 1)
        begin
            assign arb.grantee_valid = arb.requests[0];
            assign arb.grantee_v = arb.requests;
            assign arb.grantee_i = 0;
        end
        else
        begin

            //Lowest priority to current state
            always_ff @(posedge clk) begin
                if (rst)
                    state <= 0;
                else if (arb.strobe)
                    state <= arb.grantee_i;
            end

            //ex: state 0, highest priority to L2_NUM_PORTS-1
            always_comb begin
                for (int i = 0; i < L2_NUM_PORTS; i++) begin
                    muxes[i] = i;
                    for (int j = 0; j < L2_NUM_PORTS; j++) begin
                        if (arb.requests[(i+j) % L2_NUM_PORTS])
                            muxes[i] = (i+j) % L2_NUM_PORTS;
                    end
                end
            end

            //Select mux output based on current state
            assign arb.grantee_i = muxes[state];

            //Integer to one-hot
            always_comb begin
                arb.grantee_v = '0;
                arb.grantee_v[arb.grantee_i] = 1;
            end

            //any valid request
            assign  arb.grantee_valid = |arb.requests;

        end
    endgenerate

endmodule


