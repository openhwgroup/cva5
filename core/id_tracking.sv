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

import taiga_config::*;
import taiga_types::*;

module id_tracking
        (
        input logic clk,
        input logic rst,
        input logic issued,
        input logic retired,
        output logic id_available,
        output instruction_id_t oldest_id,
        output instruction_id_t next_id,
        output logic empty
        );
    //////////////////////////////////////////
    localparam LOG2_MAX_INFLIGHT_COUNT = $clog2(MAX_INFLIGHT_COUNT);
    logic [LOG2_MAX_INFLIGHT_COUNT:0] inflight_count;
    ////////////////////////////////////////////////////
    //Implementation
    always_ff @ (posedge clk) begin
        if (rst)
            oldest_id <= 0;
        else
            oldest_id <= oldest_id + LOG2_MAX_INFLIGHT_COUNT'(retired);
    end
    always_ff @ (posedge clk) begin
        if (rst)
            next_id <= 0;
        else
            next_id <= next_id + LOG2_MAX_INFLIGHT_COUNT'(issued);
    end

    //Upper bit is id_available
    always_ff @ (posedge clk) begin
        if (rst)
            inflight_count <= '1;
        else
            inflight_count <= inflight_count + (LOG2_MAX_INFLIGHT_COUNT+1)'(retired) - (LOG2_MAX_INFLIGHT_COUNT+1)'(issued);
    end

    assign empty = &inflight_count;//all ones
    assign id_available = inflight_count[LOG2_MAX_INFLIGHT_COUNT];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (rst | !(~rst & ~id_available & issued)) else $error("Issued without valid ID!");
        assert (rst | !(~rst & empty & (retired & ~issued))) else $error("Retired without any instruction inflight!");
    end
endmodule
