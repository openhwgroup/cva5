/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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
import taiga_types::*;

module fetch(
        input logic clk,
        input logic rst,

        input logic branch_flush,
        input logic gc_fetch_flush,
        input logic gc_fetch_pc_override,
        input logic exception,
        input logic [31:0] gc_fetch_pc,

        branch_predictor_interface.fetch bp,
        ras_interface.fetch ras,

        tlb_interface.mem tlb,
        local_memory_interface.master instruction_bram,
        input logic icache_on,
        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response,

        input logic pre_decode_pop,

        output logic [31:0] pre_decode_instruction,
        output logic [31:0] pre_decode_pc,
        output branch_predictor_metadata_t branch_metadata,
        output logic branch_prediction_used,
        output logic [BRANCH_PREDICTOR_WAYS-1:0] bp_update_way,
        output logic pre_decode_push
        );

    localparam NUM_SUB_UNITS = USE_I_SCRATCH_MEM + USE_ICACHE;
    localparam NUM_SUB_UNITS_W = $clog2(NUM_SUB_UNITS);

    localparam BRAM_ID = 0;
    localparam ICACHE_ID = USE_I_SCRATCH_MEM;

    fetch_sub_unit_interface fetch_sub[NUM_SUB_UNITS-1:0]();

    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;
    logic [NUM_SUB_UNITS-1:0] last_sub_unit_id;
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];
    logic [31:0] anded_unit_data_array [NUM_SUB_UNITS-1:0];

    logic units_ready;


    logic [31:0] next_pc;
    logic [31:0] if_pc;

    localparam LOG2_FETCH_BUFFER_DEPTH = $clog2(FETCH_BUFFER_DEPTH);

    logic [LOG2_FETCH_BUFFER_DEPTH:0] inflight_count;
    logic space_in_inst_buffer;
    logic mem_ready;
    logic new_mem_request;

    logic new_issue;
    logic mem_valid;

    logic delayed_flush;

    logic [31:0] stage2_phys_address;
    logic stage2_valid;

    logic update_pc;

    logic [31:0] final_instruction;


    /////////////////////////////////////////

    genvar i;
    generate
        for(i=0; i < NUM_SUB_UNITS; i++) begin
            assign unit_ready[i] = fetch_sub[i].ready;
            assign unit_data_valid[i] = fetch_sub[i].data_valid;
        end
    endgenerate
    assign units_ready = &unit_ready;

    assign update_pc = mem_ready | gc_fetch_flush;

    //Fetch PC
    always_ff @(posedge clk) begin
        if (rst)
            if_pc <= RESET_VEC;
        else if (update_pc)
            if_pc <= {next_pc[31:2], 2'b0};
    end

    always_comb begin
        if (gc_fetch_pc_override)
            next_pc = gc_fetch_pc;
        else if (branch_flush)
            next_pc = bp.branch_flush_pc;
        else if (bp.use_prediction)
            next_pc = (bp.use_ras & ras.valid) ? ras.addr : bp.predicted_pc;
        else
            next_pc = if_pc + 4;
    end

    assign bp.new_mem_request = update_pc;
    assign bp.next_pc = next_pc;

    assign bp.if_pc = if_pc;
    /*************************************
     * TLB
     *************************************/
    assign tlb.virtual_address = if_pc;
    assign tlb.execute = 1;
    assign tlb.rnw = 0;

    always_ff @(posedge clk) begin
        if (new_mem_request) begin
            stage2_phys_address <= tlb.physical_address;
        end
    end
    //////////////////////////////////////////////

    always_ff @(posedge clk) begin
        if (rst | gc_fetch_flush)
            inflight_count <= '1;
        else
            inflight_count <= inflight_count - (LOG2_FETCH_BUFFER_DEPTH+1)'(mem_ready) + (LOG2_FETCH_BUFFER_DEPTH+1)'(pre_decode_pop);
    end
    assign space_in_inst_buffer = inflight_count[LOG2_FETCH_BUFFER_DEPTH];

//assign space_in_inst_buffer = inflight_count < FETCH_BUFFER_DEPTH;
    assign mem_ready = tlb.complete & space_in_inst_buffer & units_ready;
    assign new_mem_request = mem_ready & (~gc_fetch_flush);

    //Memory interfaces
    generate if (USE_I_SCRATCH_MEM) begin
            ibram i_bram (.*, .fetch_sub(fetch_sub[BRAM_ID]));
            assign sub_unit_address_match[BRAM_ID] = (tlb.physical_address[31:32-SCRATCH_BIT_CHECK] == SCRATCH_ADDR_L[31:32-SCRATCH_BIT_CHECK]);
            assign fetch_sub[BRAM_ID].new_request = new_mem_request & (USE_ICACHE ? ~sub_unit_address_match[ICACHE_ID] : 1'b1);
            assign fetch_sub[BRAM_ID].stage1_addr = tlb.physical_address;
            assign fetch_sub[BRAM_ID].stage2_addr = stage2_phys_address;
            assign unit_data_array[BRAM_ID] = fetch_sub[BRAM_ID].data_out;
        end
    endgenerate
    generate if (USE_ICACHE) begin
            icache i_cache (.*, .fetch_sub(fetch_sub[ICACHE_ID]));
            assign sub_unit_address_match[ICACHE_ID] = tlb.physical_address[31:32-MEMORY_BIT_CHECK] == MEMORY_ADDR_L[31:32-MEMORY_BIT_CHECK];
            assign fetch_sub[ICACHE_ID].new_request = new_mem_request & sub_unit_address_match[ICACHE_ID];
            assign fetch_sub[ICACHE_ID].stage1_addr = tlb.physical_address;
            assign fetch_sub[ICACHE_ID].stage2_addr = stage2_phys_address;
            assign unit_data_array[ICACHE_ID] = fetch_sub[ICACHE_ID].data_out;

            always_ff @(posedge clk) begin
                if(rst | gc_fetch_flush)
                    stage2_valid <= 0;
                else if (mem_ready)
                    stage2_valid <= 1;
                else if (new_issue)
                    stage2_valid <= 0;
            end

            always_ff @(posedge clk) begin
                if (new_mem_request) begin
                    last_sub_unit_id <= sub_unit_address_match;
                end
            end
            //TODO potentially move support into cache so that we're not stalled on a request we no longer need due to a flush
            //If the cache is processing a miss when a flush occurs we need to discard the result once complete
            always_ff @(posedge clk) begin
                if (rst)
                    delayed_flush <= 0;
                else if (gc_fetch_flush & stage2_valid & last_sub_unit_id[ICACHE_ID] & ~fetch_sub[ICACHE_ID].data_valid)//& ~fetch_sub[ICACHE_ID].ready
                    delayed_flush <= 1;
                else if (fetch_sub[ICACHE_ID].data_valid)
                    delayed_flush <= 0;
            end
        end else begin
            assign delayed_flush = 0;
        end
    endgenerate

    assign mem_valid = ~(gc_fetch_flush | delayed_flush);
    assign new_issue =  mem_valid & (|unit_data_valid);

    //bitwise AND all subunit outputs with valid signal then or all outputs together
    always_comb begin
        final_instruction = 0;
        foreach (unit_data_array[i]) begin
            anded_unit_data_array[i] = unit_data_array[i] & {$bits(unit_data_array[i]){unit_data_valid[i]}};
            final_instruction |= anded_unit_data_array[i];
        end
    end

    ////////////////////////////////////////////////////
    //Pre-Decode Output
    assign pre_decode_instruction = final_instruction;
    assign pre_decode_pc = stage2_phys_address;
    assign pre_decode_push = new_issue;

    always_ff @(posedge clk) begin
        if (new_mem_request) begin
            branch_metadata <= bp.metadata;
            branch_prediction_used <= bp.use_prediction;
            bp_update_way <= bp.update_way;
        end
    end

endmodule
