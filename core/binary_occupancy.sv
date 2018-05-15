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

module binary_occupancy #(parameter DEPTH = 4)
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


    logic[$clog2(DEPTH)-1:0] count;

    //Occupancy Tracking
    always_ff @ (posedge clk) begin
        if (rst)
            count <= 0;
        else if (push & ~pop)
            count <= count + 1;
        else if (pop & ~push)
            count <= count - 1;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            valid <= 0;
        else if (push)
            valid <= 1;
        else if (pop && (count == 1))
            valid <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            full <= 0;
        else if ((push & ~pop) && (count == DEPTH-1))
            full <= 1;
        else if (pop)
            full <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            early_full <= 0;
        else if ((push & ~pop) && (count == DEPTH-2))
            early_full <= 1;
        else if (pop && (count == DEPTH-1))
            early_full <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            two_plus <= 0;
        else if ((push & ~pop) && (count >= 1))
            two_plus <= 1;
        else if (pop && (count == 2))
            two_plus <= 0;
    end

    assign empty = ~valid;//(count == 0);
    //assign valid = //(count != 0);
    //assign full = (count == (DEPTH-1));
    //assign early_full = (count == (DEPTH-2)) & push & ~pop;

    //pushing, or more than one, or at least one and not popping
    //assign two_plus = (count > 1);
    assign early_valid = push | (two_plus) | (valid & ~pop);

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(~rst & full & push)) else $error("overflow");
        assert (!(~rst & empty & pop)) else $error("underflow");
    end


endmodule


