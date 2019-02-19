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

import taiga_config::*;
import taiga_types::*;

module one_hot_occupancy #(parameter DEPTH = 4)
        (
        input logic clk,
        input logic rst,
        input logic push,
        input logic pop,
        output logic early_full,
        output logic full,
        output logic empty,
        output logic early_empty,
        output logic valid,
        output logic early_valid,
        output logic two_plus
        );

    logic[DEPTH:0] valid_chain;

    //Occupancy Tracking
    always_ff @ (posedge clk) begin
        if (rst) begin
            valid_chain[0] <= 1;
            valid_chain[DEPTH:1] <= 0;
        end
        else begin
            case({push,pop})
                0 : valid_chain <= valid_chain;
                1 : valid_chain <= {1'b0, valid_chain[DEPTH:1]};
                2 : valid_chain <= {valid_chain[DEPTH-1:0], 1'b0};
                3 : valid_chain <= valid_chain;
            endcase
        end
    end

    assign empty = valid_chain[0];
    assign early_empty = valid_chain[1] & pop & ~push;

    assign valid = ~valid_chain[0];
    assign full = valid_chain[DEPTH];

    assign early_full = valid_chain[DEPTH-1] | valid_chain[DEPTH];

    //pushing, or more than one, or at least one and not popping
    assign two_plus = ~valid_chain[0] & ~valid_chain[1];
    assign early_valid = push | (two_plus) | (valid & ~pop);

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(~rst & valid_chain[DEPTH] & push)) else $error("overflow");
        assert (!(~rst & valid_chain[0] & pop)) else $error("underflow");
    end

endmodule