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

import l2_config_and_types::*;

module l2_round_robin
        (
        input logic clk,
        input logic rst,
        l2_arbitration_interface.slave arb
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
                    muxes[i] = $clog2(L2_NUM_PORTS)'(i);
                    for (int j = 0; j < L2_NUM_PORTS; j++) begin
                        if (arb.requests[(i+j) % L2_NUM_PORTS])
                            muxes[i] = $clog2(L2_NUM_PORTS)'((i+j) % L2_NUM_PORTS);
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


