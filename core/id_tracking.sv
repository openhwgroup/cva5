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

    localparam MAX_INFLIGHT_COUNT_W = $clog2(MAX_INFLIGHT_COUNT+1);

    logic [MAX_INFLIGHT_COUNT_W-1:0] in_use_index;
    logic [MAX_INFLIGHT_COUNT_W-1:0] available_index;

    instruction_id_t in_use_ids [MAX_INFLIGHT_COUNT-1:0];
    instruction_id_t available_ids [MAX_INFLIGHT_COUNT-1:0];
    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    //Initial ordering, FIFO has no reset, as ID ordering is arbitrary
    initial begin
        for (int i=0; i<MAX_INFLIGHT_COUNT; i++) begin
            available_ids[i] = i[$clog2(MAX_INFLIGHT_COUNT)-1:0];
        end
    end

    //On first write will roll over to [1,00...0]
    //Upper bit indicates is the valid signal
    always_ff @ (posedge clk) begin
        if (rst) begin
            in_use_index[MAX_INFLIGHT_COUNT_W-1] <= 0;
            in_use_index[MAX_INFLIGHT_COUNT_W-2:0] <= '1;
        end else
            in_use_index <= in_use_index + MAX_INFLIGHT_COUNT_W'(issued) - MAX_INFLIGHT_COUNT_W'(retired);
    end

    //Available FIFO starts full
    always_ff @ (posedge clk) begin
        if (rst)
            available_index[MAX_INFLIGHT_COUNT_W-1:0] <= '1;
        else
            available_index <= available_index + MAX_INFLIGHT_COUNT_W'(retired) - MAX_INFLIGHT_COUNT_W'(issued);
    end

    assign empty = ~in_use_index[MAX_INFLIGHT_COUNT_W-1];
    assign id_available = available_index[MAX_INFLIGHT_COUNT_W-1];

    always_ff @ (posedge clk) begin
        if (issued)
            in_use_ids[0] <= next_id;
    end

    generate
    for (i=1 ; i < MAX_INFLIGHT_COUNT; i++) begin
        always_ff @ (posedge clk) begin
            if (issued)
                in_use_ids[i] <= in_use_ids[i-1];
        end
    end
    endgenerate

    always_ff @ (posedge clk) begin
        if (retired)
            available_ids[0] <= oldest_id;
    end

    generate
    for (i=1 ; i < MAX_INFLIGHT_COUNT; i++) begin
        always_ff @ (posedge clk) begin
            if (retired)
                available_ids[i] <= available_ids[i-1];
        end
    end
    endgenerate

    assign next_id = available_ids[available_index[MAX_INFLIGHT_COUNT_W-2:0]];
    assign oldest_id = in_use_ids[in_use_index[MAX_INFLIGHT_COUNT_W-2:0]];
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
endmodule
