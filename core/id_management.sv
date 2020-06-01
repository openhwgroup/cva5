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

module id_management

    import taiga_config::*;
    import taiga_types::*;

    (
        input logic clk,
        input logic rst,

        input logic gc_fetch_flush,

        //ID issuing
        output id_t pc_id,
        output logic pc_id_available,
        input logic pc_id_assigned,

        //Fetch stage
        output id_t fetch_id,
        input logic fetch_complete,

        //Decode stage
        input logic decode_advance,
        output id_t decode_id,
        output logic decode_id_valid,

        //Issue stage
        input id_t issue_id,
        input logic issue_stage_valid,
        input logic dummy_id_complete,
        input logic id_issued,

        //ID freeing
        input logic store_complete,
        input id_t store_id,

        input logic branch_complete,
        input id_t branch_id,

        input logic system_op_or_exception_complete,
        input id_t system_op_or_exception_id,

        input logic instruction_retired,
        input id_t retired_id
    );
    //////////////////////////////////////////
    id_t pc_id_i;
    localparam LOG2_MAX_IDS = $clog2(MAX_IDS);

    //FIFO to store IDs that have been fetched but not yet decoded
    fifo_interface #(.DATA_WIDTH(LOG2_MAX_IDS)) fetch_fifo();

    //Toggle memory blocks for tracking completion after issue
    logic decoded_toggle_mem [MAX_IDS];
    logic decoded_issued_toggle_mem [MAX_IDS];
    logic issued_toggle_mem [MAX_IDS];
    logic branch_complete_toggle_mem [MAX_IDS];
    logic store_complete_toggle_mem [MAX_IDS];
    logic system_op_or_exception_complete_toggle_mem [MAX_IDS];
    logic retired_toggle_mem [MAX_IDS];

    ////////////////////////////////////////////////////
    //Implementation

    //Next ID always increases, even on a fetch buffer flush
    //If this leads to a temporary shortage of IDs, the oldest non-issued
    //ID can be found and pc_id could be reset to that.
    assign pc_id_i = pc_id + LOG2_MAX_IDS'(pc_id_assigned);
    always_ff @ (posedge clk) begin
        if (rst)
            pc_id <= 0;
        else
            pc_id <= pc_id_i;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            fetch_id <= 0;
        else if (gc_fetch_flush)
            fetch_id <= pc_id;
        else
            fetch_id <= fetch_id + LOG2_MAX_IDS'(fetch_complete);
    end

    ////////////////////////////////////////////////////
    //Fetch buffer
    assign fetch_fifo.data_in = fetch_id;
    assign fetch_fifo.push = fetch_complete;
    assign fetch_fifo.pop = decode_advance;
    assign fetch_fifo.supress_push = 0;

    taiga_fifo #(.DATA_WIDTH(LOG2_MAX_IDS), .FIFO_DEPTH(MAX_IDS)) fetch_fifo_block (
        .fifo(fetch_fifo),
        .rst(rst | gc_fetch_flush),
        .clk
    );

    assign decode_id = fetch_fifo.data_out;
    assign decode_id_valid = fetch_fifo.valid;

    ////////////////////////////////////////////////////
    //Issue Tracking
    //As there are multiple completion sources, each source toggles a bit in its own LUTRAM.
    //All LUTRAMs are then xor-ed together to produce the status of the ID.
    //TODO: support arbitrary rst assertion (clear signal from global control)

    //Instruction decoded and (issued or flushed) pair
    initial decoded_toggle_mem = '{default: 0};
    always_ff @ (posedge clk) begin
        if (decode_advance & ~gc_fetch_flush)
            decoded_toggle_mem[decode_id] <= ~decoded_toggle_mem[decode_id];
    end

    initial decoded_issued_toggle_mem = '{default: 0};
    always_ff @ (posedge clk) begin
        if (id_issued | (gc_fetch_flush & issue_stage_valid))
            decoded_issued_toggle_mem[issue_id] <= ~decoded_issued_toggle_mem[issue_id];
    end

    //Post issue status tracking
    initial issued_toggle_mem = '{default: 0};
    always_ff @ (posedge clk) begin
        if (id_issued)
            issued_toggle_mem[issue_id] <= ~issued_toggle_mem[issue_id];
    end

    initial branch_complete_toggle_mem = '{default: 0};
    always_ff @ (posedge clk) begin
        if (branch_complete)
            branch_complete_toggle_mem[branch_id] <= ~branch_complete_toggle_mem[branch_id];
    end

    initial store_complete_toggle_mem = '{default: 0};
    always_ff @ (posedge clk) begin
        if (store_complete)
            store_complete_toggle_mem[store_id] <= ~store_complete_toggle_mem[store_id];
    end

    initial system_op_or_exception_complete_toggle_mem = '{default: 0};
    always_ff @ (posedge clk) begin
        if (system_op_or_exception_complete)
            system_op_or_exception_complete_toggle_mem[system_op_or_exception_id] <= ~system_op_or_exception_complete_toggle_mem[system_op_or_exception_id];
    end

    initial retired_toggle_mem = '{default: 0};
    always_ff @ (posedge clk) begin
        if (instruction_retired)
            retired_toggle_mem[retired_id] <= ~retired_toggle_mem[retired_id];
    end

    //Computed one cycle in advance using pc_id_i
    logic id_not_in_decode_issue;
    logic id_not_inflight;
    assign id_not_in_decode_issue = ~(decoded_toggle_mem[pc_id_i] ^ decoded_issued_toggle_mem[pc_id_i]);
    assign id_not_inflight =
        ~(issued_toggle_mem[pc_id_i] ^
            branch_complete_toggle_mem[pc_id_i] ^
            store_complete_toggle_mem[pc_id_i] ^
            system_op_or_exception_complete_toggle_mem[pc_id_i] ^
            retired_toggle_mem[pc_id_i]);

    always_ff @ (posedge clk) begin
        if (rst)
            pc_id_available <= 1;
        else
            pc_id_available <= id_not_in_decode_issue & id_not_inflight;
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    pc_id_assigned_without_pc_id_available_assertion:
        assert property (@(posedge clk) disable iff (rst) !(~pc_id_available & pc_id_assigned))
        else $error("ID assigned without any ID available");

    decode_advanced_without_id_assertion:
        assert property (@(posedge clk) disable iff (rst) !(~decode_id_valid & decode_advance))
        else $error("Decode advanced without ID");

endmodule
