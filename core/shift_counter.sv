/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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

module shift_counter

    import cva5_config::*;
    import cva5_types::*;

    #(parameter DEPTH = 16)
    (
        input logic clk,
        input logic rst,
        input logic start,
        output logic done
    );

    logic [DEPTH-1:0] counter;
    ////////////////////////////////////////////////////
    //Implementation

    //TLB_CLEAR state shift reg
    always_ff @ (posedge clk) begin
        counter[0] <= start;
        counter[DEPTH-1:1] <= counter[DEPTH-2:0];
    end
    assign done = counter[DEPTH-1];

endmodule
