/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
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

module load_store_queue //ID-based input buffer for Load/Store Unit

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;

    (
        input logic clk,
        input logic rst,

        load_store_queue_interface.queue lsq,

        //Writeback data
        input logic potential_exception,
        input instruction_id_t writeback_id,
        input logic [31:0] writeback_data,
        input logic writeback_valid
    );

    logic [MAX_INFLIGHT_COUNT-1:0] valid;
    logic [MAX_INFLIGHT_COUNT-1:0] waiting_for_data;

    instruction_id_t oldest_id;

    data_access_shared_inputs_t transactions [MAX_INFLIGHT_COUNT];
    instruction_id_t data_ids [MAX_INFLIGHT_COUNT];
    instruction_id_t data_id;

    logic [31:0] store_data [MAX_INFLIGHT_COUNT];
    logic writeback_data_match;
    logic update_store_data;

    fifo_interface #(.DATA_WIDTH($bits(instruction_id_t))) oldest_fifo ();
    ////////////////////////////////////////////////////
    //Implementation

    //Can accept an input so long as it is a load or as long as an update from writeback for an exisiting store is not in progress
    assign lsq.ready = (lsq.transaction_in.load | ~writeback_data_match);

    //FIFO to store ordering of IDs
    taiga_fifo #(.DATA_WIDTH($bits(instruction_id_t)), .FIFO_DEPTH(MAX_INFLIGHT_COUNT)) oldest_id_fifo (.fifo(oldest_fifo), .*);

    assign oldest_fifo.data_in = lsq.transaction_in.id;
    assign oldest_fifo.push = lsq.valid;
    assign oldest_fifo.supress_push = 0;
    assign oldest_fifo.pop = lsq.accepted;
    assign oldest_id = oldest_fifo.data_out;

    ////////////////////////////////////////////////////
    //Request attributes (LUTRAMs)
    always_ff @ (posedge clk) begin
        if (lsq.valid)
            transactions[lsq.transaction_in.id] <= lsq.transaction_in;
    end
    //Translation for mapping a store's ID to its needed data ID
    always_ff @ (posedge clk) begin
        if (lsq.valid)
            data_ids[lsq.transaction_in.id] <= lsq.data_valid ? lsq.transaction_in.id : lsq.data_id;
    end

    ////////////////////////////////////////////////////
    //Data Storage (LUTRAMs)
    //Check if a retiring instruction's result is needed by a store
    assign writeback_data_match = writeback_valid & waiting_for_data[writeback_id];
    assign update_store_data = (lsq.valid & lsq.data_valid) | writeback_data_match;

    always_ff @ (posedge clk) begin
        if (update_store_data)
            store_data[writeback_data_match ? writeback_id : lsq.transaction_in.id] <= writeback_data_match ? writeback_data : lsq.transaction_in.data_in;
    end

    ////////////////////////////////////////////////////
    //ID status registers
    //for whether an ID is valid and whether a store is waiting for the data from an ID
    logic [MAX_INFLIGHT_COUNT-1:0] issuing_one_hot;
    logic [MAX_INFLIGHT_COUNT-1:0] new_id_one_hot;
    logic [MAX_INFLIGHT_COUNT-1:0] need_data_one_hot;
    logic [MAX_INFLIGHT_COUNT-1:0] writeback_store_one_hot;

    always_comb begin
        new_id_one_hot = 0;
        new_id_one_hot[lsq.transaction_in.id] = lsq.valid;

        need_data_one_hot = 0;
        need_data_one_hot[lsq.data_id] = lsq.valid & ~lsq.data_valid;

        issuing_one_hot = 0;
        issuing_one_hot[oldest_id] = lsq.accepted;

        writeback_store_one_hot = 0;
        writeback_store_one_hot[writeback_id] = writeback_valid;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            valid <= 0;
        else
            valid <= (new_id_one_hot | valid) & ~issuing_one_hot;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            waiting_for_data <= 0;
        else
            waiting_for_data <= (need_data_one_hot | waiting_for_data) & ~writeback_store_one_hot;
    end

    ////////////////////////////////////////////////////
    //Output
    logic [31:0] data_for_alignment;

    assign data_id = data_ids[oldest_id];
    assign data_for_alignment = store_data[data_id];

    assign lsq.transaction_ready =  valid[oldest_id] & (lsq.transaction_out.load | ~waiting_for_data[data_id]);

    always_comb begin
        lsq.transaction_out = transactions[oldest_id];
        lsq.transaction_out.id = oldest_id;

        //Input: ABCD
        //Assuming aligned requests,
        //Possible byte selections: (A/C/D, B/D, C/D, D)
        lsq.transaction_out.data_in[7:0] = data_for_alignment[7:0];
        lsq.transaction_out.data_in[15:8] = (lsq.transaction_out.addr[1:0] == 2'b01) ? data_for_alignment[7:0] : data_for_alignment[15:8];
        lsq.transaction_out.data_in[23:16] = (lsq.transaction_out.addr[1:0] == 2'b10) ? data_for_alignment[7:0] : data_for_alignment[23:16];
        case(lsq.transaction_out.addr[1:0])
            2'b10 : lsq.transaction_out.data_in[31:24] = data_for_alignment[15:8];
            2'b11 : lsq.transaction_out.data_in[31:24] = data_for_alignment[7:0];
            default : lsq.transaction_out.data_in[31:24] = data_for_alignment[31:24];
        endcase
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
