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
        input logic store_committed,
        input instruction_id_t store_id,
        input logic [STACK_DEPTH-1:0] id_done_ordered,
        input instruction_id_t retired_id,
        output logic [$clog2(STACK_DEPTH)-1:0] ordering [STACK_DEPTH-1:0],
        output logic [$clog2(STACK_DEPTH)-1:0] ordering_post_store [STACK_DEPTH-1:0],
        output logic id_available,
        output logic [$clog2(STACK_DEPTH)-1:0] next_id,
        output logic empty
        );
    //////////////////////////////////////////
    localparam STACK_DEPTH_W = $clog2(STACK_DEPTH);

    logic [STACK_DEPTH_W-1:0] stack [STACK_DEPTH-1:0];
    logic [STACK_DEPTH_W-1:0] new_stack [STACK_DEPTH-1:0];
    logic [STACK_DEPTH_W-1:0] store_shiffted_stack_input [STACK_DEPTH-1:0];
    logic [STACK_DEPTH_W-1:0] store_shiffted_stack [STACK_DEPTH-1:0];
    logic [STACK_DEPTH_W-1:0] retired_store_shiffted_stack [STACK_DEPTH-1:0];

    logic [STACK_DEPTH-1:0] store_done_ordered;

    logic [STACK_DEPTH-1:0] store_shift_bits;
    logic [STACK_DEPTH-1:0] retired_shift_bits;

    logic [STACK_DEPTH_W:0] next_id_index;
    ////////////////////////////////////////////////////
    //Implementation

    //Initial ordering, stack has no reset, as ID ordering is arbitrary
    initial begin
        for (int i=0; i<STACK_DEPTH; i++) begin
            stack[i] = i;
        end
    end

    //TODO inorder support
    generate begin
    genvar i;
        assign store_shift_bits[0] = 1;
        assign retired_shift_bits[0] = 1;
        for (i=1; i<STACK_DEPTH; i++) begin
           assign store_shift_bits[i] = |store_done_ordered[STACK_DEPTH-1:i];
           assign retired_shift_bits[i] = |id_done_ordered[STACK_DEPTH-1:i];
        end
    end endgenerate

    always_comb begin
        //Lowest entry always shifted, each older entry shifts all below
        for (int i=0; i<STACK_DEPTH; i++) begin
            store_done_ordered[i] = (stack[i] == store_id);
        end

        //Stack shift due to stores being popped
        store_shiffted_stack_input[STACK_DEPTH-1:1] = stack[STACK_DEPTH-2:0];
        store_shiffted_stack_input[0] = store_id;
        foreach (store_shiffted_stack[i]) begin
            store_shiffted_stack[i] = (store_committed & store_shift_bits[i]) ? store_shiffted_stack_input[i] : stack[i];
        end
    end

    always_comb begin
        //Stack shift due to writes to register file being popped
        retired_store_shiffted_stack[STACK_DEPTH-1:1] = store_shiffted_stack[STACK_DEPTH-2:0];
        retired_store_shiffted_stack[0] = retired_id;
        foreach (new_stack[i]) begin
            new_stack[i] = (retired & retired_shift_bits[i]) ? retired_store_shiffted_stack[i] : store_shiffted_stack[i];
        end
    end

    //Starts at oldest entry (STACK_DEPTH-1).
    //When entry 0 is issued, id_available will become zero
    always_ff @ (posedge clk) begin
        if (rst)
            next_id_index <= '1;
        else
            next_id_index <= next_id_index + retired + store_committed - issued;
    end

    assign next_id = stack[next_id_index[STACK_DEPTH_W-1:0]];

    assign id_available = next_id_index[STACK_DEPTH_W];
    assign empty = &next_id_index;//all ones

    //Shift bits computed in parallel to retired_id in write-back
    always_ff @ (posedge clk) begin
        stack <= new_stack;
    end

    assign ordering = stack;
    assign ordering_post_store = store_shiffted_stack;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    logic entries_different = 1;
    always_comb  begin
        for (int i=0; i < STACK_DEPTH_W; i++) begin
            for (int j = i+1; j < STACK_DEPTH_W; j++) begin
                if (stack[i] == stack[j])
                    entries_different = 0;
            end
        end
    end

    always_ff @ (posedge clk) begin
        assert (1'b0) else $display("ID stack corrupted");
    end
endmodule
