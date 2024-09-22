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
        input logic fp_decode_uses_rd,
        input rs_addr_t decode_rd_addr,
        input logic decode_is_store,
        //renamer
        input phys_addr_t decode_phys_rd_addr,
        input phys_addr_t fp_decode_phys_rd_addr,

        //Issue stage
        input issue_packet_t issue,
        input logic instruction_issued,
        input logic instruction_issued_with_rd,
        input logic fp_instruction_issued_with_rd,

        //WB
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],
        input fp_wb_packet_t fp_wb_packet [2],
        output phys_addr_t wb_phys_addr [CONFIG.NUM_WB_GROUPS],
        output phys_addr_t fp_wb_phys_addr [2], 

        //Retirer
        output retire_packet_t wb_retire,
        output retire_packet_t fp_wb_retire,
        output retire_packet_t store_retire,
        output id_t retire_ids [RETIRE_PORTS],
        output logic retire_port_valid [RETIRE_PORTS],
        output logic [LOG2_RETIRE_PORTS : 0] retire_count,

        //CSR
        output logic [LOG2_MAX_IDS:0] post_issue_count
    );
    //////////////////////////////////////////
    localparam NUM_WB_GROUPS = CONFIG.NUM_WB_GROUPS + 32'(CONFIG.INCLUDE_UNIT.FPU) + 32'(CONFIG.INCLUDE_UNIT.FPU);
    logic [31:0] decode_pc;
    logic [31:0] decode_instruction;
    fetch_metadata_t decode_fetch_metadata;

    typedef enum logic[1:0] {
        NONE = 2'b00,
        RD = 2'b01,
        STORE = 2'b10,
        FP_RD = 2'b11
    } instruction_type_t;
    instruction_type_t decode_type;
    instruction_type_t retire_type [RETIRE_PORTS];

    id_t decode_id;
    id_t oldest_pre_issue_id;

    localparam ID_COUNTER_W = LOG2_MAX_IDS+1;
    logic [LOG2_MAX_IDS:0] fetched_count_neg;
    logic [LOG2_MAX_IDS:0] pre_issue_count;
    logic [LOG2_MAX_IDS:0] pre_issue_count_next;
    logic [LOG2_MAX_IDS:0] post_issue_count_next;
    logic [LOG2_MAX_IDS:0] inflight_count;

    retire_packet_t wb_retire_next;
    retire_packet_t fp_wb_retire_next;
    retire_packet_t store_retire_next;

    id_t retire_ids_next [RETIRE_PORTS];
    logic retire_port_valid_next [RETIRE_PORTS];
    logic [LOG2_RETIRE_PORTS : 0] retire_count_next;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Instruction Metadata
    //PC table(s)
    lutram_1w_1r #(.DATA_TYPE(logic[31:0]), .DEPTH(MAX_IDS))
    pc_table (
        .clk(clk),
        .waddr(pc_id),
        .raddr(decode_id),
        .ram_write(pc_id_assigned),
        .new_ram_data(if_pc),
        .ram_data_out(decode_pc)
    );

    ////////////////////////////////////////////////////
    //Instruction table
    lutram_1w_1r #(.DATA_TYPE(logic[31:0]), .DEPTH(MAX_IDS))
    instruction_table (
        .clk(clk),
        .waddr(fetch_id),
        .raddr(decode_id),
        .ram_write(fetch_complete),
        .new_ram_data(fetch_instruction),
        .ram_data_out(decode_instruction)
    );

    ////////////////////////////////////////////////////
    //Valid fetched address table
    lutram_1w_1r #(.DATA_TYPE(fetch_metadata_t), .DEPTH(MAX_IDS))
    fetch_metadata_table (
        .clk(clk),
        .waddr(fetch_id),
        .raddr(decode_id),
        .ram_write(fetch_complete),
        .new_ram_data(fetch_metadata),
        .ram_data_out(decode_fetch_metadata)
    );

    ////////////////////////////////////////////////////
    //Retire Instruction Type Table
    //Number of read ports = RETIRE_PORTS
    always_comb begin
        if (decode_uses_rd & |decode_rd_addr)
            decode_type = RD;
        else if (decode_is_store)
            decode_type = STORE;
        else if (fp_decode_uses_rd)
            decode_type = FP_RD;
        else
            decode_type = NONE;
    end
    lutram_1w_mr #(.DATA_TYPE(logic[1:0]), .DEPTH(MAX_IDS), .NUM_READ_PORTS(RETIRE_PORTS))
    retire_instruction_type_table (
        .clk(clk),
        .waddr(decode_id),
        .raddr(retire_ids_next),
        .ram_write(decode_advance),
        .new_ram_data(decode_type),
        .ram_data_out(retire_type)
    );

    ////////////////////////////////////////////////////
    //id_to_phys_rd_table
    //Number of read ports = WB_GROUPS
    id_t wb_ids [NUM_WB_GROUPS];
    phys_addr_t wb_phys_addrs [NUM_WB_GROUPS];
    always_comb begin
        wb_ids[NUM_WB_GROUPS-2] = fp_wb_packet[0].id;
        wb_ids[NUM_WB_GROUPS-1] = fp_wb_packet[1].id;
        fp_wb_phys_addr[0] = wb_phys_addrs[NUM_WB_GROUPS-2];
        fp_wb_phys_addr[1] = wb_phys_addrs[NUM_WB_GROUPS-1];
        
        for (int i = 0; i < CONFIG.NUM_WB_GROUPS; i++) begin
            //This will overwrite the FP packets if the configuration does not include it
            wb_ids[i] = wb_packet[i].id;
            wb_phys_addr[i] = wb_phys_addrs[i];
        end
    end
    
    lutram_1w_mr #(.DATA_TYPE(phys_addr_t), .DEPTH(MAX_IDS), .NUM_READ_PORTS(NUM_WB_GROUPS))
    id_to_phys_rd_table (
        .clk(clk),
        .waddr(decode_id),
        .raddr(wb_ids),
        .ram_write(decode_advance),
        .new_ram_data(fp_decode_uses_rd ? fp_decode_phys_rd_addr : decode_phys_rd_addr),
        .ram_data_out(wb_phys_addrs)
    );

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
            pc_id <= early_branch_flush ? fetch_id + LOG2_MAX_IDS'(fetch_complete) : pc_id + LOG2_MAX_IDS'(pc_id_assigned);
            fetch_id <= fetch_id + LOG2_MAX_IDS'(fetch_complete);
            decode_id <= decode_id + LOG2_MAX_IDS'(decode_advance);
        end
    end
    //Retire IDs
    //Each retire port lags behind the previous one by one index (eg. [3, 2, 1, 0])
     generate for (genvar i = 0; i < RETIRE_PORTS; i++) begin :gen_retire_ids
        always_ff @ (posedge clk) begin
            if (rst)
                retire_ids_next[i] <= LOG2_MAX_IDS'(i);
            else
                retire_ids_next[i] <= retire_ids_next[i] + LOG2_MAX_IDS'(retire_count_next);
        end

        always_ff @ (posedge clk)
            retire_ids[i] <= retire_ids_next[i];
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

    assign post_issue_count_next = post_issue_count + ID_COUNTER_W'(instruction_issued) - ID_COUNTER_W'(retire_count_next);
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

    logic id_waiting_toggle [NUM_WB_GROUPS];
    id_t id_waiting_toggle_addr [NUM_WB_GROUPS];
    always_comb begin
        id_waiting_toggle[0] = (instruction_issued_with_rd & issue.is_multicycle) | fp_instruction_issued_with_rd;
        id_waiting_toggle_addr[0] = issue.id;

        id_waiting_toggle[NUM_WB_GROUPS-2] = fp_wb_packet[0].valid;
        id_waiting_toggle_addr[NUM_WB_GROUPS-2] = fp_wb_packet[0].id;
        id_waiting_toggle[NUM_WB_GROUPS-1] = fp_wb_packet[1].valid;
        id_waiting_toggle_addr[NUM_WB_GROUPS-1] = fp_wb_packet[1].id;

        //This will overwrite the FP packets if the configuration does not include it
        for (int i = 1; i < CONFIG.NUM_WB_GROUPS; i++) begin
            id_waiting_toggle[i] = wb_packet[i].valid;
            id_waiting_toggle_addr[i] = wb_packet[i].id;
        end
    end

    toggle_memory_set # (
        .DEPTH (MAX_IDS),
        .NUM_WRITE_PORTS (NUM_WB_GROUPS),
        .NUM_READ_PORTS (RETIRE_PORTS)
    ) id_waiting_for_writeback_toggle_mem_set
    (
        .clk (clk),
        .init_clear (gc.init_clear),
        .toggle (id_waiting_toggle),
        .toggle_addr (id_waiting_toggle_addr),
        .read_addr (retire_ids_next),
        .in_use (id_waiting_for_writeback)
    );

    ////////////////////////////////////////////////////
    //Retirer
    logic contiguous_retire;
    logic id_is_post_issue [RETIRE_PORTS];
    logic id_ready_to_retire [RETIRE_PORTS];
    logic [LOG2_RETIRE_PORTS-1:0] retire_with_rd_sel;
    logic [LOG2_RETIRE_PORTS-1:0] retire_with_fp_rd_sel;
    logic [LOG2_RETIRE_PORTS-1:0] retire_with_store_sel;

    //Supports retiring up to RETIRE_PORTS instructions.  The retired block of instructions must be
    //contiguous and must start with the first retire port.  Additionally, only one register file writing 
    //instruction is supported per cycle.
    logic retire_with_rd_found;
    logic retire_with_fp_rd_found;
    logic retire_with_store_found;
    always_comb begin
        contiguous_retire = 1;
        retire_with_rd_found = 0;
        retire_with_fp_rd_found = 0;
        retire_with_store_found = 0;

        retire_with_rd_sel = 0;
        retire_with_fp_rd_sel = 0;
        retire_with_store_sel = 0;
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            id_is_post_issue[i] = post_issue_count > ID_COUNTER_W'(i);

            id_ready_to_retire[i] = (id_is_post_issue[i] & contiguous_retire & ~id_waiting_for_writeback[i]);
            retire_port_valid_next[i] = id_ready_to_retire[i] & ~((retire_type[i] == RD & retire_with_rd_found) | (retire_type[i] == STORE & retire_with_store_found) | (retire_type[i] == FP_RD & retire_with_fp_rd_found));
     
            retire_with_rd_found |= retire_port_valid_next[i] & retire_type[i] == RD;
            retire_with_fp_rd_found |= retire_port_valid_next[i] & retire_type[i] == FP_RD;
            retire_with_store_found |= retire_port_valid_next[i] & retire_type[i] == STORE;
            contiguous_retire &= retire_port_valid_next[i];

            if (retire_port_valid_next[i] & retire_type[i] == RD)
                retire_with_rd_sel = LOG2_RETIRE_PORTS'(i);
            if (retire_port_valid_next[i] & retire_type[i] == FP_RD)
                retire_with_fp_rd_sel = LOG2_RETIRE_PORTS'(i);
            if (retire_port_valid_next[i] & retire_type[i] == STORE)
                retire_with_store_sel = LOG2_RETIRE_PORTS'(i);
        end
    end

    //retire_next packets
    assign wb_retire_next = '{
        id : retire_ids_next[retire_with_rd_sel],
        valid : retire_with_rd_found
    };
    assign fp_wb_retire_next = '{
        id : retire_ids_next[retire_with_fp_rd_sel],
        valid : retire_with_fp_rd_found
    };
    assign store_retire_next = '{
        id : retire_ids_next[retire_with_store_sel],
        valid : retire_with_store_found
    };

    always_comb begin
        retire_count_next = 0;
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            retire_count_next += retire_port_valid_next[i];
        end
    end

    always_ff @ (posedge clk) begin
        wb_retire <= wb_retire_next;
        fp_wb_retire <= fp_wb_retire_next;
        store_retire <= store_retire_next;

        retire_count <= retire_count_next;
        for (int i = 0; i < RETIRE_PORTS; i++)
            retire_port_valid[i] <= retire_port_valid_next[i];
    end

    ////////////////////////////////////////////////////
    //Outputs
    assign pc_id_available = ~inflight_count[LOG2_MAX_IDS];

    //Decode
    localparam fetch_metadata_t ADDR_OK = '{ok : 1, error_code : INST_ADDR_MISSALIGNED};
    assign decode = '{
        id : decode_id,
        valid : fetched_count_neg[LOG2_MAX_IDS],
        pc : decode_pc,
        instruction : decode_instruction,
        fetch_metadata : CONFIG.MODES != BARE ? decode_fetch_metadata : ADDR_OK
    };

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
