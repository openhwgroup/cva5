/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

module fetch

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        input logic branch_flush,
        input gc_outputs_t gc,
        input logic tlb_on,
        input logic exception,

        //ID Support
        input id_t pc_id,
        input logic pc_id_available,
        output logic pc_id_assigned,
        output logic fetch_complete,
        output fetch_metadata_t fetch_metadata,

        branch_predictor_interface.fetch bp,
        ras_interface.fetch ras,

        //Instruction Metadata
        output logic early_branch_flush,
        output logic early_branch_flush_ras_adjust,
        output logic [31:0] if_pc,
        output logic [31:0] fetch_instruction,

        tlb_interface.requester tlb,
        local_memory_interface.master instruction_bram,
        input logic icache_on,
        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response,

        //Trace Interface
        output logic tr_early_branch_correction
    );

    localparam NUM_SUB_UNITS = int'(CONFIG.INCLUDE_ILOCAL_MEM) + int'(CONFIG.INCLUDE_ICACHE);
    localparam NUM_SUB_UNITS_W = (NUM_SUB_UNITS == 1) ? 1 : $clog2(NUM_SUB_UNITS);

    localparam BRAM_ID = 0;
    localparam ICACHE_ID = int'(CONFIG.INCLUDE_ILOCAL_MEM);

    localparam NEXT_ID_DEPTH = CONFIG.INCLUDE_ICACHE ? 2 : 1;

    //Subunit signals
    fetch_sub_unit_interface #(.BASE_ADDR(CONFIG.ILOCAL_MEM_ADDR.L), .UPPER_BOUND(CONFIG.ILOCAL_MEM_ADDR.H)) bram();
    fetch_sub_unit_interface #(.BASE_ADDR(CONFIG.ICACHE_ADDR.L), .UPPER_BOUND(CONFIG.ICACHE_ADDR.H)) cache();

    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];

    logic units_ready;
    logic address_valid;

    typedef struct packed{
        logic is_predicted_branch_or_jump;
        logic is_branch;
        logic address_valid;
        logic mmu_fault;
        logic [NUM_SUB_UNITS_W-1:0] subunit_id;
    } fetch_attributes_t;
    fetch_attributes_t fetch_attr_next;
    fetch_attributes_t fetch_attr;

    logic [31:0] pc_plus_4;
    logic [31:0] pc_mux [4];
    logic [1:0] pc_sel;
    logic [31:0] next_pc;
    logic [31:0] pc;

    logic flush_or_rst;
    fifo_interface #(.DATA_WIDTH($bits(fetch_attributes_t))) fetch_attr_fifo();

    logic update_pc;
    logic new_mem_request;
    logic exception_pending;

    logic [31:0] translated_address;

    //Cache related
    logic [31:0] stage2_phys_address;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation
    ////////////////////////////////////////////////////
    //Fetch PC
    assign update_pc = new_mem_request | gc.fetch_flush | early_branch_flush;
    always_ff @(posedge clk) begin
        if (gc.init_clear)
            pc <= CONFIG.CSRS.RESET_VEC;
        else if (update_pc)
            pc <= {next_pc[31:2], 2'b0};
    end

    assign pc_plus_4 = pc + 4;

    priority_encoder #(.WIDTH(4))
    pc_sel_encoder (
        .priority_vector ({1'b1, (bp.use_prediction & ~early_branch_flush), branch_flush, gc.pc_override}),
        .encoded_result (pc_sel)
    );
    assign pc_mux[0] = gc.pc;
    assign pc_mux[1] = bp.branch_flush_pc;
    assign pc_mux[2] = bp.is_return ? ras.addr : bp.predicted_pc;
    assign pc_mux[3] = pc_plus_4;
    assign next_pc = pc_mux[pc_sel];

    //If an exception occurs here in the fetch logic,
    //hold the fetching of data from memory until the status of the
    //exception has been resolved
    always_ff @(posedge clk) begin
        if (flush_or_rst)
            exception_pending <= 0;
        else if (tlb.is_fault | (new_mem_request & ~address_valid))
            exception_pending <= 1;
    end

    assign bp.new_mem_request = update_pc;
    assign bp.next_pc = next_pc;
    assign bp.if_pc = pc;
    assign bp.pc_id = pc_id;
    assign bp.pc_id_assigned = pc_id_assigned;

    assign ras.pop = bp.use_prediction & bp.is_return & ~branch_flush & ~gc.pc_override & new_mem_request & (~early_branch_flush);
    assign ras.push = bp.use_prediction & bp.is_call & ~branch_flush & ~gc.pc_override & new_mem_request & (~early_branch_flush);
    assign ras.new_addr = pc_plus_4;
    assign ras.branch_fetched = bp.use_prediction & bp.is_branch & new_mem_request & (~early_branch_flush); //flush not needed as FIFO resets inside of RAS

    ////////////////////////////////////////////////////
    //TLB
    assign tlb.virtual_address = pc;
    assign tlb.execute = 1;
    assign tlb.rnw = 0;
    assign tlb.new_request = tlb.ready & (CONFIG.INCLUDE_S_MODE & tlb_on);
    assign translated_address = (CONFIG.INCLUDE_S_MODE & tlb_on) ? tlb.physical_address : pc;

    always_ff @(posedge clk) begin
        if (new_mem_request)
            stage2_phys_address <= translated_address;
    end

    //////////////////////////////////////////////
    //Issue Control Signals
    assign flush_or_rst = (rst | gc.fetch_flush | early_branch_flush);

    assign new_mem_request = (~tlb_on | tlb.done) & pc_id_available & units_ready & (~gc.fetch_hold) & (~exception_pending);
    assign pc_id_assigned = new_mem_request | tlb.is_fault;

    //////////////////////////////////////////////
    //Subunit Tracking
    assign fetch_attr_fifo.push = new_mem_request | tlb.is_fault;
    assign fetch_attr_fifo.potential_push = new_mem_request | tlb.is_fault;
    assign fetch_attr_fifo.pop = fetch_complete;
    one_hot_to_integer #(NUM_SUB_UNITS)
    hit_way_conv (
        .one_hot    (sub_unit_address_match), 
        .int_out    (fetch_attr_next.subunit_id)
    );
    assign fetch_attr_next.is_predicted_branch_or_jump = bp.use_prediction;
    assign fetch_attr_next.is_branch = bp.use_prediction & bp.is_branch;
    assign fetch_attr_next.address_valid = address_valid;
    assign fetch_attr_next.mmu_fault = tlb.is_fault;

    assign fetch_attr_fifo.data_in = fetch_attr_next;

    taiga_fifo #(.DATA_WIDTH($bits(fetch_attributes_t)), .FIFO_DEPTH(NEXT_ID_DEPTH))
    attributes_fifo (
        .clk        (clk), 
        .rst        (flush_or_rst), 
        .fifo       (fetch_attr_fifo)
    );

    assign fetch_attr = fetch_attr_fifo.data_out;

    ////////////////////////////////////////////////////
    //Subunit Interfaces
    //In the case of a gc.fetch_flush, a request may already be in progress
    //for any sub unit.  That request can either be completed or aborted.
    //In either case, data_valid must NOT be asserted.
    generate if (CONFIG.INCLUDE_ILOCAL_MEM) begin
        assign sub_unit_address_match[BRAM_ID] = bram.address_range_check(translated_address);
        assign unit_ready[BRAM_ID] = bram.ready;
        assign unit_data_valid[BRAM_ID] = bram.data_valid;
        assign bram.new_request = new_mem_request & sub_unit_address_match[BRAM_ID];
        assign bram.stage1_addr = translated_address;
        assign bram.stage2_addr = stage2_phys_address;
        assign bram.flush = gc.fetch_flush;
        assign unit_data_array[BRAM_ID] = bram.data_out;

        ibram i_bram (
            .clk (clk), 
            .rst (rst),
            .fetch_sub (bram),
            .instruction_bram (instruction_bram)
        );
    end
    endgenerate
    generate if (CONFIG.INCLUDE_ICACHE) begin
        assign sub_unit_address_match[ICACHE_ID] = cache.address_range_check(translated_address);
        assign unit_ready[ICACHE_ID] = cache.ready;
        assign unit_data_valid[ICACHE_ID] = cache.data_valid;
        assign cache.new_request = new_mem_request & sub_unit_address_match[ICACHE_ID];
        assign cache.stage1_addr = translated_address;
        assign cache.stage2_addr = stage2_phys_address;
        assign cache.flush = gc.fetch_flush;
        assign unit_data_array[ICACHE_ID] = cache.data_out;
        icache #(.CONFIG(CONFIG))
        i_cache (
            .clk (clk), 
            .rst (rst),
            .icache_on (icache_on),
            .l1_request (l1_request),
            .l1_response (l1_response),
            .fetch_sub (cache)
        );
    end
    endgenerate

    assign units_ready = &unit_ready;
    assign address_valid = |sub_unit_address_match;

    ////////////////////////////////////////////////////
    //Instruction metada updates
    logic valid_fetch_result;
    assign valid_fetch_result = fetch_attr_fifo.valid & fetch_attr.address_valid & (~fetch_attr.mmu_fault);

    assign if_pc = pc;
    assign fetch_metadata.ok = valid_fetch_result;
    assign fetch_metadata.error_code = fetch_attr.mmu_fault ? FETCH_PAGE_FAULT : FETCH_ACCESS_FAULT;

    assign fetch_instruction = unit_data_array[fetch_attr.subunit_id];
    assign fetch_complete = (fetch_attr_fifo.valid & ~valid_fetch_result) | (|unit_data_valid);//allow instruction to propagate to decode if address is invalid

    ////////////////////////////////////////////////////
    //Branch Predictor correction
    logic is_branch_or_jump;
    assign is_branch_or_jump = fetch_instruction[6:2] inside {JAL_T, JALR_T, BRANCH_T};
    assign early_branch_flush = (valid_fetch_result & (|unit_data_valid)) & fetch_attr.is_predicted_branch_or_jump & (~is_branch_or_jump);
    assign early_branch_flush_ras_adjust = (valid_fetch_result & (|unit_data_valid)) & fetch_attr.is_branch & (~is_branch_or_jump);
    generate if (ENABLE_TRACE_INTERFACE) begin
        assign tr_early_branch_correction = early_branch_flush;
    end endgenerate

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    spurious_fetch_complete_assertion:
        assert property (@(posedge clk) disable iff (rst) (|unit_data_valid) |-> (fetch_attr_fifo.valid && unit_data_valid[fetch_attr.subunit_id]))
        else $error("Spurious fetch complete detected!");

endmodule
