/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

//This module requires the input always be encoded as a one-hot signal
//as all possible conditions are ORed together
module one_hot_to_integer
    #(
        parameter C_WIDTH = 40
    )
    (
        input logic [C_WIDTH-1:0] one_hot,
        output logic [(C_WIDTH == 1) ? 0 : ($clog2(C_WIDTH)-1) : 0] int_out
    );
    ////////////////////////////////////////////////////
    //Implementation    
    generate if (C_WIDTH == 1) begin : gen_width_one
        assign int_out = 0;
    end else begin : gen_width_two_plus
        always_comb begin
            int_out = 0;
            foreach(one_hot[i])
                int_out |= one_hot[i] ? $clog2(C_WIDTH)'(i) : 0;
        end
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Assertions
    // always_ff @ (posedge clk) begin
    //    assert (rst || (~rst && $onehot0(one_hot))) else $error("One-hot signal has multiple bits set!");
    //end

endmodule
