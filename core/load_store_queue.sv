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
        input logic gc_fetch_flush,
        input logic gc_issue_flush,

        load_store_queue_interface.queue lsq,
        writeback_store_interface.ls wb_store,

        output logic ready_for_forwarded_store
    );

    logic [MAX_IDS-1:0] valid;
    id_t oldest_id;

    typedef struct packed {
        logic [31:0] addr;
        logic load;
        logic store;
        logic [3:0] be;
        logic [2:0] fn3;
        logic [31:0] data_in;
        id_t id;
        logic forwarded_store;
        id_t data_id;
    } lsq_entry_t;

    lsq_entry_t new_lsq_entry;
    logic [$bits(lsq_entry_t)-1:0] lsq_entries [MAX_IDS];
    lsq_entry_t oldest_lsq_entry;

    fifo_interface #(.DATA_WIDTH($bits(id_t))) oldest_fifo ();
    ////////////////////////////////////////////////////
    //Implementation

    //Can always buffer new requests
    assign lsq.ready = 1;

    //FIFO to store ordering of IDs
    taiga_fifo #(.DATA_WIDTH($bits(id_t)), .FIFO_DEPTH(MAX_IDS)) oldest_id_fifo (
        .clk, .rst(rst | gc_issue_flush),
        .fifo(oldest_fifo)
    );

    assign oldest_fifo.data_in = lsq.id;
    assign oldest_fifo.push = lsq.new_issue;
    assign oldest_fifo.potential_push = lsq.possible_issue;
    assign oldest_fifo.pop = lsq.accepted;
    assign oldest_id = oldest_fifo.data_out;

    assign lsq.empty = ~oldest_fifo.valid;

    ////////////////////////////////////////////////////
    //Request attributes and input data (LUTRAMs)
    always_comb begin
        new_lsq_entry.addr = lsq.addr;
        new_lsq_entry.load = lsq.load;
        new_lsq_entry.store = lsq.store;
        new_lsq_entry.be = lsq.be;
        new_lsq_entry.fn3 = lsq.fn3;
        new_lsq_entry.data_in = lsq.data_in;
        new_lsq_entry.id = lsq.id;
        new_lsq_entry.forwarded_store = lsq.forwarded_store;
        new_lsq_entry.data_id = lsq.data_id;
    end

    always_ff @ (posedge clk) begin
        if (lsq.possible_issue)
            lsq_entries[lsq.id] <= new_lsq_entry;
    end

    ////////////////////////////////////////////////////
    //ID status registers
    //for whether an ID is valid
    // logic [MAX_INFLIGHT_COUNT-1:0] issuing_one_hot;
    // logic [MAX_INFLIGHT_COUNT-1:0] new_id_one_hot;

    // always_comb begin
    //     new_id_one_hot = 0;
    //     new_id_one_hot[lsq.id] = lsq.new_issue;

    //     issuing_one_hot = 0;
    //     issuing_one_hot[oldest_id] = lsq.accepted;
    // end

    // set_clr_reg_with_rst #(.SET_OVER_CLR(0), .WIDTH(MAX_INFLIGHT_COUNT), .RST_VALUE('0)) valid_m (
    //   .clk, .rst,
    //   .set(new_id_one_hot),
    //   .clr(issuing_one_hot),
    //   .result(valid)
    // );

    ////////////////////////////////////////////////////
    //Store Forwarding Support
    //Only a single store can be forwarded at any given time
    //The needed result is registered at the writeback stage when the 
    //needed ID is retired.
    logic possible_new_forwarded_store;//To help shorten logic path for registering results in the writeback stage
    logic new_forwarded_store;
    logic forwarded_store_complete;
    id_t needed_id_r;
    logic waiting_r;

    assign possible_new_forwarded_store = lsq.possible_issue & lsq.forwarded_store;
    assign new_forwarded_store = lsq.new_issue & lsq.forwarded_store;
    assign forwarded_store_complete = lsq.accepted & oldest_lsq_entry.forwarded_store;

    always_ff @ (posedge clk) begin
        if (rst)
            waiting_r <= 0;
        else
            waiting_r <= new_forwarded_store | (waiting_r & ~wb_store.id_done);
    end
    assign wb_store.waiting = new_forwarded_store | waiting_r;
    assign wb_store.possibly_waiting = possible_new_forwarded_store | waiting_r;

    assign wb_store.ack = forwarded_store_complete;
    assign ready_for_forwarded_store = ~(waiting_r | wb_store.id_done);

    always_ff @ (posedge clk) begin
        if (new_forwarded_store)
            needed_id_r <= lsq.data_id;
    end
    assign wb_store.id_needed = possible_new_forwarded_store ? lsq.data_id : needed_id_r;



    ////////////////////////////////////////////////////
    //Output
    logic [31:0] data_for_alignment;

    assign oldest_lsq_entry = lsq_entries[oldest_id];
    assign lsq.transaction_ready =  oldest_fifo.valid & (~oldest_lsq_entry.forwarded_store | wb_store.id_done);
    assign lsq.id_needed_by_store = oldest_lsq_entry.data_id;

    always_comb begin
        lsq.transaction_out.addr = oldest_lsq_entry.addr;
        lsq.transaction_out.load = oldest_lsq_entry.load;
        lsq.transaction_out.store = oldest_lsq_entry.store;
        lsq.transaction_out.be = oldest_lsq_entry.be;
        lsq.transaction_out.fn3 = oldest_lsq_entry.fn3;
        lsq.transaction_out.id = oldest_id;

        data_for_alignment = oldest_lsq_entry.forwarded_store ? wb_store.data : oldest_lsq_entry.data_in;
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
