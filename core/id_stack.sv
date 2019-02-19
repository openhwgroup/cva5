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

module id_stack # (
        parameter STACK_DEPTH = 4
        )
        (
        input logic clk,
        input logic rst,
        input logic issued,
        input logic retired,
        input logic [STACK_DEPTH-1:0] shift_bits,
        input logic [$clog2(STACK_DEPTH)-1:0] retired_id,
        output logic [$clog2(STACK_DEPTH)-1:0] ordering [STACK_DEPTH-1:0],
        output logic id_available,
        output logic [$clog2(STACK_DEPTH)-1:0] next_id
        );
    //////////////////////////////////////////
    localparam STACK_DEPTH_W = $clog2(STACK_DEPTH);

    logic [STACK_DEPTH_W-1:0] stack [STACK_DEPTH-1:0];
    logic [STACK_DEPTH_W-1:0] stack_shift_input [STACK_DEPTH-1:0];

    logic [STACK_DEPTH_W:0] oldest_valid;
    //////////////////////////////////////////

    //Initial ordering, stack has no reset, as ID ordering is arbitrary
    initial begin
        for (int i=0; i<STACK_DEPTH; i++) begin
            stack[i] = i;
        end
    end

    always_comb begin
        stack_shift_input[3:1] = stack[2:0];
        stack_shift_input[0] = retired_id;
    end

    assign next_id = stack[oldest_valid[STACK_DEPTH_W-1:0]];

    //Starts at oldest entry (STACK_DEPTH-1).
    //When entry 0 is issued, id_available will become zero
    always_ff @ (posedge clk) begin
        if (rst) begin
            oldest_valid <= '1;
        end else
            oldest_valid <= oldest_valid + retired - issued;
    end
    assign id_available = oldest_valid[STACK_DEPTH_W];

    //Shift bits computed in parallel to retired_id in write-back
    always_ff @ (posedge clk) begin
        foreach (stack[i]) begin
            if (retired)
                stack[i] <= shift_bits[i] ? stack_shift_input[i] : stack[i];
        end
    end

    assign ordering = stack;

endmodule
