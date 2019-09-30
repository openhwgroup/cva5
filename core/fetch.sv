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
    localparam NUM_SUB_UNITS_W = (NUM_SUB_UNITS == 1) ? 1 : $clog2(NUM_SUB_UNITS);

    localparam BRAM_ID = 0;
    localparam ICACHE_ID = USE_I_SCRATCH_MEM;

    localparam FETCH_BUFFER_DEPTH_W = $clog2(FETCH_BUFFER_DEPTH);
    localparam NEXT_ID_DEPTH = USE_ICACHE ? 2 : 1;

    //Subunit signals
    fetch_sub_unit_interface fetch_sub[NUM_SUB_UNITS-1:0]();
    logic [NUM_SUB_UNITS-1:0] sub_unit_address_match;
    logic [NUM_SUB_UNITS-1:0] last_sub_unit_id;
    logic [NUM_SUB_UNITS-1:0] unit_ready;
    logic [NUM_SUB_UNITS-1:0] unit_data_valid;
    logic [31:0] unit_data_array [NUM_SUB_UNITS-1:0];
    logic [31:0] anded_unit_data_array [NUM_SUB_UNITS-1:0];

    logic units_ready;
    logic units_data_valid;

    logic [31:0] next_pc;
    logic [31:0] pc;

    logic flush_or_rst;
    logic [FETCH_BUFFER_DEPTH_W:0] inflight_count;
    fifo_interface #(.DATA_WIDTH(NUM_SUB_UNITS_W)) next_unit();
    logic space_in_inst_buffer;
    logic new_mem_request;

    //Cache related
    logic delayed_flush;
    logic [31:0] stage2_phys_address;
    logic stage2_valid;

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

    always_comb begin
        if (branch_flush)
            next_pc = bp.branch_flush_pc;
        else if (gc_fetch_pc_override)
            next_pc = gc_fetch_pc;
        else if (bp.use_prediction)
            next_pc = (bp.use_ras & ras.valid) ? ras.addr : bp.predicted_pc;
        else
            next_pc = pc + 4;
    end

    assign bp.new_mem_request = new_mem_request | gc_fetch_flush;
    assign bp.next_pc = next_pc;

    assign bp.if_pc = pc;

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

    always_ff @(posedge clk) begin
        if (flush_or_rst)
            inflight_count <= '1;
        else
            inflight_count <= inflight_count - (FETCH_BUFFER_DEPTH_W+1)'(new_mem_request) + (FETCH_BUFFER_DEPTH_W+1)'(pre_decode_pop);
    end

    assign space_in_inst_buffer = inflight_count[FETCH_BUFFER_DEPTH_W];
    assign new_mem_request = tlb.complete & space_in_inst_buffer & units_ready;

    //////////////////////////////////////////////
    //Subunit Tracking
    assign next_unit.push = new_mem_request;
    assign next_unit.pop = units_data_valid;
    one_hot_to_integer #(NUM_SUB_UNITS) hit_way_conv (.*, .one_hot(sub_unit_address_match), .int_out(next_unit.data_in));
    taiga_fifo #(.DATA_WIDTH(NUM_SUB_UNITS_W), .FIFO_DEPTH(NEXT_ID_DEPTH))
        attributes_fifo (.fifo(next_unit), .rst(flush_or_rst), .*);

    ////////////////////////////////////////////////////
    //Subunit Interfaces
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
        assign sub_unit_address_match[BRAM_ID] = USE_ICACHE ? ~sub_unit_address_match[ICACHE_ID] : 1'b1;
    end
    endgenerate
    generate if (USE_ICACHE) begin
        icache i_cache (.*, .fetch_sub(fetch_sub[ICACHE_ID]));
        assign sub_unit_address_match[ICACHE_ID] = tlb.physical_address[31:32-MEMORY_BIT_CHECK] == MEMORY_ADDR_L[31:32-MEMORY_BIT_CHECK];

        always_ff @(posedge clk) begin
            if(flush_or_rst)
                stage2_valid <= 0;
            else if (new_mem_request)
                stage2_valid <= 1;
            else if (pre_decode_push)
                stage2_valid <= 0;
        end

        always_ff @(posedge clk) begin
            if (new_mem_request)
                last_sub_unit_id <= sub_unit_address_match;
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

    ////////////////////////////////////////////////////
    //Pre-Decode Output
    assign pre_decode_instruction = unit_data_array[next_unit.data_out];
    assign pre_decode_pc = stage2_phys_address;
    assign pre_decode_push = (~delayed_flush) & units_data_valid;//FIFO is cleared on gc_fetch_flush

    always_ff @(posedge clk) begin
        if (new_mem_request) begin
            branch_metadata <= bp.metadata;
            branch_prediction_used <= bp.use_prediction;
            bp_update_way <= bp.update_way;
        end
    end

endmodule
