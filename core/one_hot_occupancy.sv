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

module one_hot_occupancy #(parameter DEPTH = 2)
        (
        input logic clk,
        input logic rst,
        input logic push,
        input logic pop,
        output logic early_full,
        output logic full,
        output logic empty,
        output logic valid,
        output logic early_valid,
        output logic two_plus
        );


    logic[DEPTH:0] valid_chain;

    //Occupancy Tracking
    always_ff @ (posedge clk) begin
        if (rst)
            valid_chain <= 1;
        else if (push & ~pop)
            valid_chain <= {valid_chain[DEPTH-1:0], 1'b0};
        else if (pop & ~push)
            valid_chain <= {1'b0, valid_chain[DEPTH:1]};
    end

    assign empty = valid_chain[0];
    assign valid = ~valid_chain[0];
    assign full = valid_chain[DEPTH];

//    always_ff @ (posedge clk) begin
//        if (rst)
//            early_full <= 0;
//        else if (push & ~pop & valid_chain[DEPTH-2])
//            early_full <= 1;
//        else if (pop & ~push & valid_chain[DEPTH-1])
//            early_full <= 0;
//    end


    assign early_full = valid_chain[DEPTH-1] | valid_chain[DEPTH];

    //pushing, or more than one, or at least one and not popping
    always_ff @ (posedge clk) begin
        if (rst)
            two_plus <= 0;
        else if ((valid & push) & ~pop)
            two_plus <= 1;
        else if (~push & (two_plus & pop))
            two_plus <= 0;
    end

   // assign two_plus = ~valid_chain[0] & ~valid_chain[1];
    assign early_valid = push | (two_plus) | (valid & ~pop);

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(~rst & valid_chain[DEPTH] & push)) else $error("overflow");
        assert (!(~rst & valid_chain[0] & pop)) else $error("underflow");
    end


endmodule

