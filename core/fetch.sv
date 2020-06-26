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

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fetch(
        input logic clk,
        input logic rst,

        input logic branch_flush,
        input logic gc_fetch_hold,
        input logic gc_fetch_flush,
        input logic gc_fetch_pc_override,
        input logic exception,
        input logic [31:0] gc_fetch_pc,

        //ID Support
        input logic pc_id_available,
        output logic pc_id_assigned,
        output logic fetch_complete,

        branch_predictor_interface.fetch bp,
        ras_interface.fetch ras,

        //Instruction Metadata
        output logic [31:0] if_pc,
        output logic [31:0] fetch_instruction,

        tlb_interface.mem tlb,
        local_memory_interface.master instruction_bram,
        input logic icache_on,
        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response
        );

    localparam NUM_SUB_UNITS = USE_I_SCRATCH_MEM + USE_ICACHE;
    localparam NUM_SUB_UNITS_W = (NUM_SUB_UNITS == 1) ? 1 : $clog2(NUM_SUB_UNITS);

    localparam BRAM_ID = 0;
    localparam ICACHE_ID = USE_I_SCRATCH_MEM;

    localparam NEXT_ID_DEPTH = USE_ICACHE ? 2 : 1;

    //Subunit signals
    fetch_sub_unit_interface fetch_sub[NUM_SUB_UNITS-1:0]();
    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];

    logic units_ready;
    logic units_data_valid;

    logic [31:0] next_pc;
    logic [31:0] pc;

    logic flush_or_rst;
    fifo_interface #(.DATA_WIDTH(NUM_SUB_UNITS_W)) next_unit();

    logic new_mem_request;

    //Cache related
    logic [31:0] stage2_phys_address;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation
    ////////////////////////////////////////////////////
    //Fetch PC
    always_ff @(posedge clk) begin
        if (rst)
            pc <= RESET_VEC;
        else if (new_mem_request | gc_fetch_flush)
            pc <= {next_pc[31:2], 2'b0};
    end

    logic [31:0] pc_plus_4;
    assign pc_plus_4 = pc + 4;
    always_comb begin
        if (gc_fetch_pc_override)
            next_pc = gc_fetch_pc;
        else if (branch_flush)
            next_pc = bp.branch_flush_pc;
        else if (bp.use_prediction)
            next_pc = bp.is_return ? ras.addr : bp.predicted_pc;
        else
            next_pc = pc_plus_4;
    end

    assign bp.new_mem_request = new_mem_request | gc_fetch_flush;
    assign bp.next_pc = next_pc;
    assign bp.if_pc = pc;

    assign ras.pop = bp.use_prediction & bp.is_return & ~branch_flush & ~gc_fetch_pc_override & new_mem_request;
    assign ras.push = bp.use_prediction & bp.is_call & ~branch_flush & ~gc_fetch_pc_override & new_mem_request;
    assign ras.new_addr = pc_plus_4;
    assign ras.branch_fetched = bp.use_prediction & bp.is_branch & new_mem_request; //flush not needed as FIFO resets inside of RAS

    ////////////////////////////////////////////////////
    //TLB
    assign tlb.virtual_address = pc;
    assign tlb.execute = 1;
    assign tlb.rnw = 0;

    always_ff @(posedge clk) begin
        if (new_mem_request)
            stage2_phys_address <= tlb.physical_address;
    end

    //////////////////////////////////////////////
    //Issue Control Signals
    assign flush_or_rst = (rst | gc_fetch_flush);

    assign new_mem_request = tlb.complete & pc_id_available & units_ready & ~gc_fetch_hold;
    assign pc_id_assigned = new_mem_request & ~gc_fetch_flush;

    //////////////////////////////////////////////
    //Subunit Tracking
    assign next_unit.push = new_mem_request;
    assign next_unit.potential_push = new_mem_request;
    assign next_unit.pop = units_data_valid;
    one_hot_to_integer #(NUM_SUB_UNITS) hit_way_conv (.*, .one_hot(sub_unit_address_match), .int_out(next_unit.data_in));
    taiga_fifo #(.DATA_WIDTH(NUM_SUB_UNITS_W), .FIFO_DEPTH(NEXT_ID_DEPTH))
        attributes_fifo (.fifo(next_unit), .rst(flush_or_rst), .*);

    ////////////////////////////////////////////////////
    //Subunit Interfaces
    //In the case of a gc_fetch_flush, a request may already be in progress
    //for any sub unit.  That request can either be completed or aborted.
    //In either case, data_valid must NOT be asserted.
    logic cache_address_match;
    generate
        for (i = 0; i < NUM_SUB_UNITS; i++) begin
            assign unit_ready[i] = fetch_sub[i].ready;
            assign unit_data_valid[i] = fetch_sub[i].data_valid;
            assign fetch_sub[i].new_request = new_mem_request & sub_unit_address_match[i];
            assign fetch_sub[i].stage1_addr = tlb.physical_address;
            assign fetch_sub[i].stage2_addr = stage2_phys_address;
            assign fetch_sub[i].flush = gc_fetch_flush;
            assign unit_data_array[i] = fetch_sub[i].data_out;
        end
    endgenerate
    assign units_ready = &unit_ready;
    assign units_data_valid = |unit_data_valid;

    generate if (USE_I_SCRATCH_MEM) begin
        ibram i_bram (.*, .fetch_sub(fetch_sub[BRAM_ID]));
        assign sub_unit_address_match[BRAM_ID] = USE_ICACHE ? ~cache_address_match : 1'b1;
    end
    endgenerate
    generate if (USE_ICACHE) begin
        icache i_cache (.*, .fetch_sub(fetch_sub[ICACHE_ID]));
        assign cache_address_match = tlb.physical_address[31:32-MEMORY_BIT_CHECK] == MEMORY_ADDR_L[31:32-MEMORY_BIT_CHECK];
        assign sub_unit_address_match[ICACHE_ID] = cache_address_match;
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Instruction metada updates
    assign if_pc = pc;
    assign fetch_instruction = unit_data_array[next_unit.data_out];
    assign fetch_complete = units_data_valid;

endmodule
