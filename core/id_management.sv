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
        input issue_packet_t issue,
        input logic instruction_issued,
        input id_t rs_id[REGFILE_READ_PORTS],
        output logic rs_id_inuse[REGFILE_READ_PORTS],

        //ID freeing
        input logic store_complete,
        input id_t store_id,

        input logic branch_complete,
        input id_t branch_id,

        input logic system_op_or_exception_complete,
        input logic exception_with_rd_complete,
        input id_t system_op_or_exception_id,

        input id_t ids_retiring [COMMIT_PORTS],
        input logic retired [COMMIT_PORTS],

        output logic [$clog2(MAX_COMPLETE_COUNT)-1:0] retire_inc
    );
    //////////////////////////////////////////
    id_t pc_id_i;
    localparam LOG2_MAX_IDS = $clog2(MAX_IDS);

    //FIFO to store IDs that have been fetched but not yet decoded
    fifo_interface #(.DATA_WIDTH(LOG2_MAX_IDS)) fetch_fifo();

    //Toggle memory results for tracking completion after issue
    logic decoded_status;
    logic decoded_issued_status;

    logic issued_status;
    logic issued_status_rs [REGFILE_READ_PORTS];

    logic branch_complete_status;
    logic store_complete_status;

    logic system_op_or_exception_complete_status;
    logic exception_with_rd_complete_status_rs [REGFILE_READ_PORTS];

    logic [COMMIT_PORTS-1:0] retired_status;
    logic [COMMIT_PORTS-1:0] retired_status_rs [REGFILE_READ_PORTS];

    logic [$clog2(MAX_COMPLETE_COUNT)-1:0] complete_count;
    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    //Next ID always increases, except on a fetch buffer flush.
    //On a fetch buffer flush, the next ID is restored to the current decode ID.
    //This prevents a stall in the case where all  IDs are either in-flight or
    //in the fetch buffer at the point of a fetch flush.
    assign pc_id_i = pc_id + LOG2_MAX_IDS'(pc_id_assigned);
    always_ff @ (posedge clk) begin
        if (rst)
            pc_id <= 0;
        else if (gc_fetch_flush)
            pc_id <= decode_id_valid ? decode_id : pc_id;
        else
            pc_id <= pc_id_i;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            fetch_id <= 0;
        else if (gc_fetch_flush)
            fetch_id <= decode_id_valid ? decode_id : pc_id;
        else
            fetch_id <= fetch_id + LOG2_MAX_IDS'(fetch_complete);
    end

    ////////////////////////////////////////////////////
    //Fetch buffer
    assign fetch_fifo.data_in = fetch_id;
    assign fetch_fifo.push = fetch_complete;
    assign fetch_fifo.potential_push = fetch_complete;
    assign fetch_fifo.pop = decode_advance;

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
    toggle_memory decode_toggle_mem (
        .clk, .rst,
        .toggle(decode_advance & ~gc_fetch_flush),
        .toggle_id(decode_id),
        .read_id(pc_id_i),
        .read_data(decoded_status)
    );

    toggle_memory decoded_issued_toggle_mem (
        .clk, .rst,
        .toggle(instruction_issued | (gc_fetch_flush & issue.stage_valid)),
        .toggle_id(issue.id),
        .read_id(pc_id_i),
        .read_data(decoded_issued_status)
    );

    //Post issue status tracking
    toggle_memory issued_toggle_mem (
        .clk, .rst,
        .toggle(instruction_issued),
        .toggle_id(issue.id),
        .read_id(pc_id_i),
        .read_data(issued_status)
    );
    generate for (i = 0; i < REGFILE_READ_PORTS; i++) begin
        toggle_memory issued_toggle_mem_rs (
            .clk, .rst,
            .toggle(instruction_issued & issue.uses_rd),
            .toggle_id(issue.id),
            .read_id(rs_id[i]),
            .read_data(issued_status_rs[i])
        );
    end endgenerate

    toggle_memory branch_toggle_mem (
        .clk, .rst,
        .toggle(branch_complete),
        .toggle_id(branch_id),
        .read_id(pc_id_i),
        .read_data(branch_complete_status)
    );

    toggle_memory store_toggle_mem (
        .clk, .rst,
        .toggle(store_complete),
        .toggle_id(store_id),
        .read_id(pc_id_i),
        .read_data(store_complete_status)
    );

    toggle_memory system_op_or_exception_complete_toggle_mem (
        .clk, .rst,
        .toggle(system_op_or_exception_complete),
        .toggle_id(system_op_or_exception_id),
        .read_id(pc_id_i),
        .read_data(system_op_or_exception_complete_status)
    );

    generate for (i = 0; i < REGFILE_READ_PORTS; i++) begin
        toggle_memory exception_complete_toggle_mem_rs (
            .clk, .rst,
            .toggle(exception_with_rd_complete),
            .toggle_id(system_op_or_exception_id),
            .read_id(rs_id[i]),
            .read_data(exception_with_rd_complete_status_rs[i])
        );
    end endgenerate

    //One memory per commit port
    genvar j;
    generate for (i = 0; i < COMMIT_PORTS; i++) begin
        toggle_memory retired_toggle_mem (
            .clk, .rst,
            .toggle(retired[i]),
            .toggle_id(ids_retiring[i]),
            .read_id(pc_id_i),
            .read_data(retired_status[i])
        );
        for (j = 0; j < REGFILE_READ_PORTS; j++) begin
            toggle_memory retired_toggle_mem_rs (
                .clk, .rst,
                .toggle(retired[i]),
                .toggle_id(ids_retiring[i]),
                .read_id(rs_id[j]),
                .read_data(retired_status_rs[j][i])
            );
        end
    end endgenerate

    //Computed one cycle in advance using pc_id_i
    logic id_not_in_decode_issue;
    logic id_not_inflight;
    assign id_not_in_decode_issue = ~(decoded_status ^ decoded_issued_status);
    assign id_not_inflight =
        ~(issued_status ^
            branch_complete_status ^
            store_complete_status ^
            system_op_or_exception_complete_status ^
            (^retired_status)
        );

    //rs1/rs2 conflicts don't check branch or store memories as the only
    //IDs stored in the rs to ID table are instructions that write to the register file
    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            rs_id_inuse[i] = (
                issued_status_rs[i] ^
                exception_with_rd_complete_status_rs[i] ^
                (^retired_status_rs[i])
            );
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            pc_id_available <= 1;
        else
            pc_id_available <= id_not_in_decode_issue & id_not_inflight;
    end

    localparam MCC_W = $clog2(MAX_COMPLETE_COUNT);
    always_comb begin
        complete_count = MCC_W'(branch_complete) + MCC_W'(store_complete) + MCC_W'(system_op_or_exception_complete);
        for (int i = 0; i < COMMIT_PORTS; i++) begin
            complete_count  += MCC_W'(retired[i]);
        end
    end
    always_ff @ (posedge clk) begin
        retire_inc <= complete_count;
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
