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
    localparam INUSE_COUNTER_W = $clog2(MAX_INFLIGHT_COUNT+1);

    logic [INUSE_COUNTER_W-1:0] inuse_index;
    instruction_id_t inuse_ids [MAX_INFLIGHT_COUNT-1:0];

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    //Initial ordering, FIFO has no reset, as ID ordering is arbitrary
    initial begin
        for (int i=0; i<MAX_INFLIGHT_COUNT; i++) begin
            inuse_ids[i] = i[$clog2(MAX_INFLIGHT_COUNT)-1:0];
        end
    end

    //Upper bit is id_available
    always_ff @ (posedge clk) begin
        if (rst)
            inuse_index <= '1;
        else
            inuse_index <= inuse_index + INUSE_COUNTER_W'(retired) - INUSE_COUNTER_W'(issued);
    end

    assign empty = &inuse_index;//all ones
    assign id_available = inuse_index[INUSE_COUNTER_W-1];

    assign next_id = inuse_ids[inuse_index[INUSE_COUNTER_W-2:0]];
    assign oldest_id = inuse_ids[MAX_INFLIGHT_COUNT-1];

    always_ff @ (posedge clk) begin
        if (retired)
            inuse_ids[0] <= inuse_ids[MAX_INFLIGHT_COUNT-1];
    end

    generate
    for (i=1 ; i < MAX_INFLIGHT_COUNT; i++) begin
        always_ff @ (posedge clk) begin
            if (retired)
                inuse_ids[i] <= inuse_ids[i-1];
        end
    end
    endgenerate
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(~id_available & issued)) else $error("Issued without valid ID!");
        assert (!(empty & (retired & ~issued))) else $error("Retired without any instruction inflight!");
    end
endmodule
