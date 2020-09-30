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

module instruction_metadata_and_id_management

    import taiga_config::*;
    import taiga_types::*;

    (
        input logic clk,
        input logic rst,

        input logic gc_init_clear,
        input logic gc_fetch_flush,

        //Fetch
        output id_t pc_id,
        output logic pc_id_available,
        input logic [31:0] if_pc,
        input logic pc_id_assigned,

        output id_t fetch_id,
        input logic early_branch_flush,
        input logic fetch_complete,
        input logic [31:0] fetch_instruction,
        input fetch_metadata_t fetch_metadata,

        //Decode ID
        output decode_packet_t decode,
        input logic decode_advance,

        //Issue stage
        input issue_packet_t issue,
        input logic instruction_issued,
        output id_t rs_id [REGFILE_READ_PORTS],
        output logic rs_inuse [REGFILE_READ_PORTS],
        output logic rs_id_inuse[REGFILE_READ_PORTS],

        //Branch Predictor
        input branch_metadata_t branch_metadata_if,
        output branch_metadata_t branch_metadata_ex,

        //ID freeing
        input logic store_complete,
        input id_t store_id,

        input logic branch_complete,
        input id_t branch_id,

        input logic system_op_or_exception_complete,
        input logic exception_with_rd_complete,
        input id_t system_op_or_exception_id,

        output logic [$clog2(MAX_COMPLETE_COUNT)-1:0] retire_inc,

        //Writeback/Register File
        input id_t ids_retiring [COMMIT_PORTS],
        input logic retired [COMMIT_PORTS],
        output logic [4:0] retired_rd_addr [COMMIT_PORTS],
        output id_t id_for_rd [COMMIT_PORTS],
        //Exception
        output logic [31:0] exception_pc

    );
    //////////////////////////////////////////
    logic [31:0] pc_table [MAX_IDS];
    logic [31:0] instruction_table [MAX_IDS];
    logic valid_fetch_addr_table [MAX_IDS];

    logic [4:0] rd_addr_table [MAX_IDS];
    logic [$bits(branch_metadata_t)-1:0] branch_metadata_table [MAX_IDS];
    logic [$bits(fetch_metadata_t)-1:0] fetch_metadata_table [MAX_IDS];

    localparam LOG2_MAX_IDS = $clog2(MAX_IDS);
    id_t clear_index;
    id_t pc_id_next;
    id_t decode_id;
    logic [LOG2_MAX_IDS:0] fetched_count; //MSB used as valid for decode stage

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

    logic id_not_in_decode_issue;
    logic id_not_inflight;

    //Writes to register file
    id_t rd_to_id_table [32];
    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Instruction Metadata
    //pc table
    always_ff @ (posedge clk) begin
        if (pc_id_assigned)
            pc_table[pc_id] <= if_pc;
    end

    //branch metadata table
    always_ff @ (posedge clk) begin
        if (pc_id_assigned)
            branch_metadata_table[pc_id] <= branch_metadata_if;
    end

    //instruction table
    always_ff @ (posedge clk) begin
        if (fetch_complete)
            instruction_table[fetch_id] <= fetch_instruction;
    end

    //rd table
    always_ff @ (posedge clk) begin
        if (fetch_complete)
            rd_addr_table[fetch_id] <= fetch_instruction[11:7];
    end

    //valid fetched address table
    always_ff @ (posedge clk) begin
        if (fetch_complete)
            fetch_metadata_table[fetch_id] <= fetch_metadata;
    end
    

    //Operand inuse determination
    initial rd_to_id_table = '{default: 0};
    always_ff @ (posedge clk) begin
        if (instruction_issued & issue.uses_rd)//tracks most recently issued instruction that writes to the register file
            rd_to_id_table[issue.rd_addr] <= issue.id;
    end

    ////////////////////////////////////////////////////
    //ID Management

    //Post-reset clr
    initial clear_index = 0;
    always_ff @ (posedge clk) begin
        if (gc_init_clear)
            clear_index <= clear_index + 1;
    end
    
    //Next ID always increases, except on a fetch buffer flush.
    //On a fetch buffer flush, the next ID is restored to the current decode ID.
    //This prevents a stall in the case where all  IDs are either in-flight or
    //in the fetch buffer at the point of a fetch flush.
    id_t next_pc_id_base;
    id_t next_fetch_id_base;
    assign next_pc_id_base = gc_fetch_flush ? decode_id : (early_branch_flush ? fetch_id : pc_id);
    assign next_fetch_id_base = gc_fetch_flush ? decode_id : fetch_id;

    assign pc_id_next = gc_init_clear ? clear_index : 
        (next_pc_id_base + LOG2_MAX_IDS'({pc_id_assigned & ~gc_fetch_flush}));
    always_ff @ (posedge clk) begin
        if (rst) begin
            pc_id <= 0;
            fetch_id <= 0;
            decode_id <= 0;
        end
        else begin
            pc_id <= next_pc_id_base + LOG2_MAX_IDS'({pc_id_assigned & (~gc_fetch_flush)});
            fetch_id <= next_fetch_id_base + LOG2_MAX_IDS'({fetch_complete & ~gc_fetch_flush});
            decode_id <= decode_id + LOG2_MAX_IDS'({decode_advance & ~gc_fetch_flush});
        end
    end

    always_ff @ (posedge clk) begin
        if (rst | gc_fetch_flush)
            fetched_count <= 0;
        else
            fetched_count <= fetched_count + (LOG2_MAX_IDS+1)'(decode_advance) - (LOG2_MAX_IDS+1)'(fetch_complete);
    end

    ////////////////////////////////////////////////////
    //Issue Tracking
    //As there are multiple completion sources, each source toggles a bit in its own LUTRAM.
    //All LUTRAMs are then xor-ed together to produce the status of the ID.
    //TODO: support arbitrary rst assertion (clear signal from global control)

    //Instruction decoded and (issued or flushed) pair
    toggle_memory #(.DEPTH(MAX_IDS)) decode_toggle_mem (
        .clk, .rst,
        .toggle((gc_init_clear & ~id_not_in_decode_issue) | (decode_advance & ~gc_fetch_flush)),
        .toggle_id(gc_init_clear ? clear_index : decode.id),
        .read_id(pc_id_next),
        .read_data(decoded_status)
    );

    toggle_memory #(.DEPTH(MAX_IDS)) decoded_issued_toggle_mem (
        .clk, .rst,
        .toggle(instruction_issued | (gc_fetch_flush & issue.stage_valid)),
        .toggle_id(issue.id),
        .read_id(pc_id_next),
        .read_data(decoded_issued_status)
    );

    //Post issue status tracking
    toggle_memory #(.DEPTH(MAX_IDS)) issued_toggle_mem (
        .clk, .rst,
        .toggle((gc_init_clear & ~id_not_inflight)  | instruction_issued),
        .toggle_id(gc_init_clear ? clear_index : issue.id),
        .read_id(pc_id_next),
        .read_data(issued_status)
    );
    generate for (i = 0; i < REGFILE_READ_PORTS; i++) begin
        toggle_memory #(.DEPTH(MAX_IDS)) issued_toggle_mem_rs (
            .clk, .rst,
            .toggle((gc_init_clear & rs_id_inuse[i]) | (instruction_issued & issue.uses_rd)),
            .toggle_id(gc_init_clear ? clear_index : issue.id),
            .read_id(rs_id[i]),
            .read_data(issued_status_rs[i])
        );
    end endgenerate

    toggle_memory #(.DEPTH(MAX_IDS)) branch_toggle_mem (
        .clk, .rst,
        .toggle(branch_complete),
        .toggle_id(branch_id),
        .read_id(pc_id_next),
        .read_data(branch_complete_status)
    );

    toggle_memory #(.DEPTH(MAX_IDS)) store_toggle_mem (
        .clk, .rst,
        .toggle(store_complete),
        .toggle_id(store_id),
        .read_id(pc_id_next),
        .read_data(store_complete_status)
    );

    toggle_memory system_op_or_exception_complete_toggle_mem (
        .clk, .rst,
        .toggle(system_op_or_exception_complete),
        .toggle_id(system_op_or_exception_id),
        .read_id(pc_id_next),
        .read_data(system_op_or_exception_complete_status)
    );

    generate for (i = 0; i < REGFILE_READ_PORTS; i++) begin
        toggle_memory #(.DEPTH(MAX_IDS)) exception_complete_toggle_mem_rs (
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
        toggle_memory #(.DEPTH(MAX_IDS)) retired_toggle_mem (
            .clk, .rst,
            .toggle(retired[i]),
            .toggle_id(ids_retiring[i]),
            .read_id(pc_id_next),
            .read_data(retired_status[i])
        );
        for (j = 0; j < REGFILE_READ_PORTS; j++) begin
            toggle_memory #(.DEPTH(MAX_IDS)) retired_toggle_mem_rs (
                .clk, .rst,
                .toggle(retired[i]),
                .toggle_id(ids_retiring[i]),
                .read_id(rs_id[j]),
                .read_data(retired_status_rs[j][i])
            );
        end
    end endgenerate

    //Computed one cycle in advance using pc_id_next

    assign id_not_in_decode_issue = ~(decoded_status ^ decoded_issued_status);
    assign id_not_inflight =
        ~(issued_status ^
            branch_complete_status ^
            store_complete_status ^
            system_op_or_exception_complete_status ^
            (^retired_status)
        );

    ////////////////////////////////////////////////////
    //Outputs

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

    //Decode
    assign decode.id = decode_id;
    assign decode.valid = fetched_count[LOG2_MAX_IDS];
    assign decode.pc = pc_table[decode_id];
    assign decode.instruction = instruction_table[decode_id];
    assign decode.fetch_metadata = fetch_metadata_table[decode_id];

    //Branch Predictor
    assign branch_metadata_ex = branch_metadata_table[branch_id];

    //Issue
    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            rs_id[i] = gc_init_clear ? clear_index : rd_to_id_table[issue.rs_addr[i]];
            rs_inuse[i] = (|issue.rs_addr[i]) & (issue.rs_addr[i] == rd_addr_table[rs_id[i]]);
        end
    end

    //Writeback support
    always_comb begin
        retired_rd_addr[0] = issue.rd_addr;
        for (int i = 1; i < COMMIT_PORTS; i++) begin
            retired_rd_addr[i] = rd_addr_table[ids_retiring[i]];
        end
    end
    always_comb begin
        for (int i = 0; i < COMMIT_PORTS; i++) begin
            id_for_rd[i] = rd_to_id_table[retired_rd_addr[i]];
        end
    end

    //Exception Support
     generate if (ENABLE_M_MODE) begin
         assign exception_pc = pc_table[system_op_or_exception_id];
     end endgenerate

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    pc_id_assigned_without_pc_id_available_assertion:
        assert property (@(posedge clk) disable iff (rst) !(~pc_id_available & pc_id_assigned))
        else $error("ID assigned without any ID available");

    decode_advanced_without_id_assertion:
        assert property (@(posedge clk) disable iff (rst) !(~decode.valid & decode_advance))
        else $error("Decode advanced without ID");

endmodule
