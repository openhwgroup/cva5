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

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

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
        input logic decode_uses_rd,
        input rs_addr_t decode_rd_addr,
        input exception_sources_t decode_exception_unit,
        //renamer
        input phys_addr_t decode_phys_rd_addr,

        //Issue stage
        input issue_packet_t issue,
        input logic instruction_issued,
        input logic instruction_issued_with_rd,

        //WB
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],
        output commit_packet_t commit_packet [CONFIG.NUM_WB_GROUPS],

        //Retirer
        output retire_packet_t retire,
        output id_t retire_ids [RETIRE_PORTS],
        output id_t retire_ids_next [RETIRE_PORTS],
        output logic retire_port_valid [RETIRE_PORTS],

        //CSR
        output logic [LOG2_MAX_IDS:0] post_issue_count,
        //Exception
        output logic [31:0] oldest_pc,
        output logic [$clog2(NUM_EXCEPTION_SOURCES)-1:0] current_exception_unit
    );
    //////////////////////////////////////////
    (* ramstyle = "MLAB, no_rw_check" *) logic [31:0] pc_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [31:0] instruction_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] valid_fetch_addr_table [MAX_IDS];

    (* ramstyle = "MLAB, no_rw_check" *) phys_addr_t phys_addr_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] uses_rd_table [MAX_IDS];

    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(fetch_metadata_t)-1:0] fetch_metadata_table [MAX_IDS];

    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(exception_sources_t)-1:0] exception_unit_table [MAX_IDS];

    id_t decode_id;
    id_t oldest_pre_issue_id;

    localparam ID_COUNTER_W = LOG2_MAX_IDS+1;
    logic [LOG2_MAX_IDS:0] fetched_count_neg;
    logic [LOG2_MAX_IDS:0] pre_issue_count;
    logic [LOG2_MAX_IDS:0] pre_issue_count_next;
    logic [LOG2_MAX_IDS:0] post_issue_count_next;
    logic [LOG2_MAX_IDS:0] inflight_count;

    retire_packet_t retire_next;
    logic retire_port_valid_next [RETIRE_PORTS];

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Instruction Metadata
    //PC table
    //Number of read ports = 1 or 2 (decode stage + exception logic (if enabled))
    always_ff @ (posedge clk) begin
        if (pc_id_assigned)
            pc_table[pc_id] <= if_pc;
    end

    ////////////////////////////////////////////////////
    //Instruction table
    //Number of read ports = 1 (decode stage)
    always_ff @ (posedge clk) begin
        if (fetch_complete)
            instruction_table[fetch_id] <= fetch_instruction;
    end

    ////////////////////////////////////////////////////
    //Valid fetched address table
    //Number of read ports = 1 (decode stage)
    always_ff @ (posedge clk) begin
        if (fetch_complete)
            fetch_metadata_table[fetch_id] <= fetch_metadata;
    end

    ////////////////////////////////////////////////////
    //Phys rd table
    //Number of read ports = (NUM_WB_GROUPS - 1)  (ALU WB group uses issue_phys_rd_addr)
    always_ff @ (posedge clk) begin
        if (decode_advance)
            phys_addr_table[decode_id] <= decode_phys_rd_addr;
    end

    ////////////////////////////////////////////////////
    //Uses rd table
    //Number of read ports = RETIRE_PORTS
    always_ff @ (posedge clk) begin
        if (decode_advance)
            uses_rd_table[decode_id] <= decode_uses_rd & |decode_rd_addr;
    end

    ////////////////////////////////////////////////////
    //Exception unit table
    always_ff @ (posedge clk) begin
        if (decode_advance)
            exception_unit_table[decode_id] <= decode_exception_unit;
    end

    ////////////////////////////////////////////////////
    //ID Management
    
    //Next ID always increases, except on a fetch buffer flush.
    //On a fetch buffer flush, the next ID is restored to the oldest non-issued ID (decode or issue stage)
    //This prevents a stall in the case where all  IDs are either in-flight or
    //in the fetch buffer at the point of a fetch flush.
    always_ff @ (posedge clk) begin
        if (rst)
            oldest_pre_issue_id <= 0;
        else if (instruction_issued)
            oldest_pre_issue_id <= oldest_pre_issue_id + 1;
    end

    always_ff @ (posedge clk) begin
        if (gc.fetch_flush) begin
            pc_id <= oldest_pre_issue_id;
            fetch_id <= oldest_pre_issue_id;
            decode_id <= oldest_pre_issue_id;
        end
        else begin
            pc_id <= (early_branch_flush ? fetch_id : pc_id) + LOG2_MAX_IDS'(pc_id_assigned);
            fetch_id <= fetch_id + LOG2_MAX_IDS'(fetch_complete);
            decode_id <= decode_id + LOG2_MAX_IDS'(decode_advance);
        end
    end
    //Retire IDs
    //Each retire port lags behind the previous one by one index (eg. [3, 2, 1, 0])
     generate for (i = 0; i < RETIRE_PORTS; i++) begin :gen_retire_ids
        always_ff @ (posedge clk) begin
            if (rst)
                retire_ids_next[i] <= LOG2_MAX_IDS'(i);
            else
                retire_ids_next[i] <= retire_ids_next[i] + LOG2_MAX_IDS'(retire_next.count);
        end

        always_ff @ (posedge clk) begin
            if (~gc.retire_hold)
                retire_ids[i] <= retire_ids_next[i];
        end
        
    end endgenerate

    //Represented as a negative value so that the MSB indicates that the decode stage is valid
    always_ff @ (posedge clk) begin
        if (gc.fetch_flush)
            fetched_count_neg <= 0;
        else
            fetched_count_neg <= fetched_count_neg + ID_COUNTER_W'(decode_advance) - ID_COUNTER_W'(fetch_complete);
    end

    //Full instruction count split into two: pre-issue and post-issue
    //pre-issue count can be cleared on a fetch flush
    //post-issue count decremented only on retire
    assign pre_issue_count_next = pre_issue_count  + ID_COUNTER_W'(pc_id_assigned) - ID_COUNTER_W'(instruction_issued);
    always_ff @ (posedge clk) begin
        if (gc.fetch_flush)
            pre_issue_count <= 0;
        else
            pre_issue_count <= pre_issue_count_next;
    end

    assign post_issue_count_next = post_issue_count + ID_COUNTER_W'(instruction_issued) - ID_COUNTER_W'(retire_next.count);
    always_ff @ (posedge clk) begin
        if (rst)
            post_issue_count <= 0;
        else
            post_issue_count <= post_issue_count_next;
    end

    always_ff @ (posedge clk) begin
        if (gc.fetch_flush)
            inflight_count <= post_issue_count_next;
        else
            inflight_count <= pre_issue_count_next + post_issue_count_next;
    end

    ////////////////////////////////////////////////////
    //ID in-use determination
    logic id_waiting_for_writeback [RETIRE_PORTS];
    //WB group zero is not included as it completes within a single cycle
    //Non-writeback instructions not included as current instruction set
    //complete in their first cycle of the execute stage, or do not cause an
    //exception after that point
    toggle_memory_set # (
        .DEPTH (MAX_IDS),
        .NUM_WRITE_PORTS (2),
        .NUM_READ_PORTS (RETIRE_PORTS),
        .WRITE_INDEX_FOR_RESET (0),
        .READ_INDEX_FOR_RESET (0)
    ) id_waiting_for_writeback_toggle_mem_set
    (
        .clk (clk),
        .rst (rst),
        .init_clear (gc.init_clear),
        .toggle ('{(instruction_issued_with_rd & issue.is_multicycle), wb_packet[1].valid}),
        .toggle_addr ('{issue.id, wb_packet[1].id}),
        .read_addr (retire_ids_next),
        .in_use (id_waiting_for_writeback)
    );

    ////////////////////////////////////////////////////
    //Retirer
    logic contiguous_retire;
    logic id_is_post_issue [RETIRE_PORTS];
    logic id_ready_to_retire [RETIRE_PORTS];
    logic [LOG2_RETIRE_PORTS-1:0] phys_id_sel;
    logic [RETIRE_PORTS-1:0] retire_id_uses_rd;
    logic [RETIRE_PORTS-1:0] retire_id_waiting_for_writeback;

     generate for (i = 0; i < RETIRE_PORTS; i++) begin : gen_retire_writeback
        assign retire_id_uses_rd[i] = uses_rd_table[retire_ids_next[i]];
        assign retire_id_waiting_for_writeback[i] = id_waiting_for_writeback[i];
     end endgenerate

    //Supports retiring up to RETIRE_PORTS instructions.  The retired block of instructions must be
    //contiguous and must start with the first retire port.  Additionally, only one register file writing 
    //instruction is supported per cycle.
    //If an exception is pending, only retire a single intrustuction per cycle.  As such, the pending
    //exception will have to become the oldest instruction retire_ids[0] before it can retire.
    logic retire_with_rd_found;
    always_comb begin
        contiguous_retire = ~gc.retire_hold;
        retire_with_rd_found = 0;
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            id_is_post_issue[i] = post_issue_count > ID_COUNTER_W'(i);

            id_ready_to_retire[i] = (id_is_post_issue[i] & contiguous_retire & ~id_waiting_for_writeback[i]);
            retire_port_valid_next[i] = id_ready_to_retire[i] & ~(retire_id_uses_rd[i] & retire_with_rd_found);
     
            retire_with_rd_found |= retire_port_valid_next[i] & retire_id_uses_rd[i];
            contiguous_retire &= retire_port_valid_next[i] & ~gc.exception_pending;
        end
    end

    //retire_next packet
    priority_encoder #(.WIDTH(RETIRE_PORTS))
    phys_id_sel_encoder (
        .priority_vector (retire_id_uses_rd),
        .encoded_result (phys_id_sel)
    );
    assign retire_next.phys_id = retire_ids_next[phys_id_sel];
    assign retire_next.valid = retire_with_rd_found;

    always_comb begin
        retire_next.count = 0;
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            retire_next.count += retire_port_valid_next[i];
        end
    end

    always_ff @ (posedge clk) begin
        retire.valid <= retire_next.valid;
        retire.phys_id <= retire_next.phys_id;
        retire.count <= gc.writeback_supress ? '0 : retire_next.count;
        for (int i = 0; i < RETIRE_PORTS; i++)
            retire_port_valid[i] <= retire_port_valid_next[i] & ~gc.writeback_supress;
    end

    ////////////////////////////////////////////////////
    //Outputs
    assign pc_id_available = ~inflight_count[LOG2_MAX_IDS];

    //Decode
    assign decode.id = decode_id;
    assign decode.valid = fetched_count_neg[LOG2_MAX_IDS];
    assign decode.pc = pc_table[decode_id];
    assign decode.instruction = instruction_table[decode_id];
    assign decode.fetch_metadata = CONFIG.INCLUDE_M_MODE ? fetch_metadata_table[decode_id] : '{ok : 1, error_code : INST_ACCESS_FAULT};

    //Writeback/Commit support
    phys_addr_t commit_phys_addr [CONFIG.NUM_WB_GROUPS];
    assign commit_phys_addr[0] = issue.phys_rd_addr;
     generate for (i = 1; i < CONFIG.NUM_WB_GROUPS; i++) begin : gen_commit_phys_addr
        assign commit_phys_addr[i] = phys_addr_table[wb_packet[i].id];
     end endgenerate

     generate for (i = 0; i < CONFIG.NUM_WB_GROUPS; i++) begin : gen_commit_packet
        assign commit_packet[i].id = wb_packet[i].id;
        assign commit_packet[i].phys_addr = commit_phys_addr[i];        
        assign commit_packet[i].valid = wb_packet[i].valid & |commit_phys_addr[i];
        assign commit_packet[i].data = wb_packet[i].data;
     end endgenerate

    //Exception Support
     generate if (CONFIG.INCLUDE_M_MODE) begin : gen_id_exception_support
        assign oldest_pc = pc_table[retire_ids_next[0]];
        assign current_exception_unit = exception_unit_table[retire_ids_next[0]];
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
