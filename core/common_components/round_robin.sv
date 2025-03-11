/*
 * Copyright © 2017 Eric Matthews, Lesley Shannon
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

module round_robin

    #(
        parameter int unsigned NUM_PORTS = 2
    ) (
        input logic clk,
        input logic rst,

        input logic[NUM_PORTS-1:0] requests,
        input logic grant,
        output logic[(NUM_PORTS == 1 ? 1 : $clog2(NUM_PORTS))-1:0] grantee
    );

    localparam PORT_W = $clog2(NUM_PORTS);

    generate if (NUM_PORTS == 1) begin : gen_no_arb
        assign grantee = '0;
    end else begin : gen_arb
        logic[PORT_W-1:0] state;
        logic[PORT_W-1:0] muxes [NUM_PORTS-1:0];

        //Lowest priority to current state
        always_ff @(posedge clk) begin
            if (rst)
                state <= 0;
            else if (grant)
                state <= grantee;
        end

        //ex: state 0, highest priority to PORTS-1
        always_comb begin
            for (int i = 0; i < NUM_PORTS; i++) begin
                muxes[i] = PORT_W'(i);
                for (int j = 0; j < NUM_PORTS; j++) begin
                    if (requests[(i + j) % NUM_PORTS])
                        muxes[i] = PORT_W'((i + j) % NUM_PORTS);
                end
            end
        end

        //Select mux output based on current state
        assign grantee = muxes[state];
    end endgenerate

endmodule
