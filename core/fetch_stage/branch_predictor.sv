/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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

module branch_predictor

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,
        branch_predictor_interface.branch_predictor bp,
        input branch_results_t br_results,
        ras_interface.branch_predictor ras
    );

    //BP tag width can be reduced, based on memory size, when virtual address
    //support is not enabled
    localparam longint CACHE_RANGE = 64'(CONFIG.ICACHE_ADDR.H) - 64'(CONFIG.ICACHE_ADDR.L) + 1;
    localparam longint SCRATCH_RANGE = 64'(CONFIG.ILOCAL_MEM_ADDR.H) - 64'(CONFIG.ILOCAL_MEM_ADDR.L) + 1;
    localparam longint BUS_RANGE = 64'(CONFIG.IBUS_ADDR.H) - 64'(CONFIG.IBUS_ADDR.L) + 1;

    function int get_memory_width();
        if(CONFIG.MODES == MSU)
            return 32;
        else if (CONFIG.INCLUDE_ICACHE && (
            (CONFIG.INCLUDE_ILOCAL_MEM && CACHE_RANGE > SCRATCH_RANGE) ||
            (CONFIG.INCLUDE_IBUS && CACHE_RANGE > BUS_RANGE) ||
            (!CONFIG.INCLUDE_ILOCAL_MEM && !CONFIG.INCLUDE_IBUS))
        )
            return $clog2(CACHE_RANGE);
        else if (CONFIG.INCLUDE_IBUS && (
            (CONFIG.INCLUDE_ILOCAL_MEM && BUS_RANGE > SCRATCH_RANGE) ||
            (!CONFIG.INCLUDE_ILOCAL_MEM))
        )
            return $clog2(BUS_RANGE);
        else
            return $clog2(SCRATCH_RANGE);
    endfunction

    localparam BRANCH_ADDR_W = $clog2(CONFIG.BP.ENTRIES);
    localparam BTAG_W = get_memory_width() - BRANCH_ADDR_W - 2;
    cache_functions_interface #(.TAG_W(BTAG_W), .LINE_W(BRANCH_ADDR_W), .SUB_LINE_W(0)) addr_utils();

    typedef logic[1:0] branch_predictor_metadata_t;
    typedef struct packed {
        logic valid;
        logic [BTAG_W-1:0] tag;
        logic is_branch;
        logic is_return;
        logic is_call;
        branch_predictor_metadata_t metadata;
    } branch_table_entry_t;

    branch_table_entry_t [CONFIG.BP.WAYS-1:0] if_entry;
    branch_table_entry_t ex_entry;

    typedef struct packed{
        branch_predictor_metadata_t branch_predictor_metadata;
        logic branch_prediction_used;
        logic [CONFIG.BP.WAYS-1:0] branch_predictor_update_way;
    } branch_metadata_t;
    branch_metadata_t branch_metadata_ex;

    logic branch_predictor_direction_changed;
    logic [31:0] new_jump_addr;
    logic [CONFIG.BP.WAYS-1:0][31:0] predicted_pc;

    logic [CONFIG.BP.WAYS-1:0] tag_matches;
    logic [CONFIG.BP.WAYS-1:0] replacement_way;
    logic [CONFIG.BP.WAYS-1:0] tag_update_way;
    logic [CONFIG.BP.WAYS-1:0] target_update_way;
    logic [$clog2(CONFIG.BP.WAYS > 1 ? CONFIG.BP.WAYS : 2)-1:0] hit_way;
    logic tag_match;
    logic use_predicted_pc;

    addr_utils_interface #(CONFIG.IBUS_ADDR.L, CONFIG.IBUS_ADDR.H) ibus_addr_utils ();

    /////////////////////////////////////////

    genvar i;
    generate if (CONFIG.INCLUDE_BRANCH_PREDICTOR) begin : gen_bp
        for (i=0; i<CONFIG.BP.WAYS; i++) begin : gen_bp_rams
            sdp_ram #(
                .ADDR_WIDTH(BRANCH_ADDR_W),
                .NUM_COL(1),
                .COL_WIDTH($bits(branch_table_entry_t)),
                .PIPELINE_DEPTH(0)
            ) tag_bank (
                .a_en(tag_update_way[i]),
                .a_wbe(tag_update_way[i]),
                .a_wdata(ex_entry),
                .a_addr(addr_utils.getHashedLineAddr(br_results.pc, i)),
                .b_en(bp.new_mem_request),
                .b_addr(addr_utils.getHashedLineAddr(bp.next_pc, i)),
                .b_rdata(if_entry[i]),
            .*);

            sdp_ram #(
                .ADDR_WIDTH(BRANCH_ADDR_W),
                .NUM_COL(1),
                .COL_WIDTH(32),
                .PIPELINE_DEPTH(0)
            ) addr_table (
                .a_en(target_update_way[i]),
                .a_wbe(target_update_way[i]),
                .a_wdata(br_results.target_pc),
                .a_addr(addr_utils.getHashedLineAddr(br_results.pc, i)),
                .b_en(bp.new_mem_request),
                .b_addr(addr_utils.getHashedLineAddr(bp.next_pc, i)),
                .b_rdata(predicted_pc[i]),
            .*);

            assign tag_matches[i] = ({if_entry[i].valid, if_entry[i].tag} == {1'b1, addr_utils.getTag(bp.if_pc)});
        end
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Instruction Fetch Response
    one_hot_to_integer #(CONFIG.BP.WAYS)
    hit_way_conv (       
        .one_hot(tag_matches), 
        .int_out(hit_way)
    );

    assign tag_match = |tag_matches;

    assign use_predicted_pc = CONFIG.INCLUDE_BRANCH_PREDICTOR & tag_match;

    //Predicted PC and whether the prediction is valid
    assign bp.predicted_pc = predicted_pc[hit_way];
    assign bp.use_prediction = use_predicted_pc;
    assign bp.is_branch = if_entry[hit_way].is_branch;
    assign bp.is_return = if_entry[hit_way].is_return;
    assign bp.is_call = if_entry[hit_way].is_call;

    ////////////////////////////////////////////////////
    //Instruction Fetch metadata
    cycler #(CONFIG.BP.WAYS)
    replacement_policy (       
        .clk (clk),
        .rst (rst), 
        .en (1'b1), 
        .one_hot (replacement_way)
    );

    lutram_1w_1r #(.DATA_TYPE(branch_metadata_t), .DEPTH(MAX_IDS))
    branch_metadata_table (
        .clk(clk),
        .waddr(bp.pc_id),
        .raddr(br_results.id),
        .ram_write(bp.pc_id_assigned),
        .new_ram_data('{
            branch_predictor_metadata : if_entry[hit_way].metadata,
            branch_prediction_used : use_predicted_pc,
            branch_predictor_update_way : tag_match ? tag_matches : replacement_way
        }),
        .ram_data_out(branch_metadata_ex)
    );

    ////////////////////////////////////////////////////
    //Execution stage update
    assign ex_entry.valid = 1;
    assign ex_entry.tag = addr_utils.getTag(br_results.pc);
    assign ex_entry.is_branch = br_results.is_branch;
    assign ex_entry.is_return = br_results.is_return;
    assign ex_entry.is_call = br_results.is_call;


    //2-bit saturating counter
    always_comb begin
        case(branch_metadata_ex.branch_predictor_metadata)
            2'b00 : ex_entry.metadata = br_results.branch_taken ? 2'b01 : 2'b00;
            2'b01 : ex_entry.metadata = br_results.branch_taken ? 2'b10 : 2'b00;
            2'b10 : ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b01;
            2'b11 : ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b10;
        endcase
        if (~branch_metadata_ex.branch_prediction_used)
            ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b00;
    end
    assign branch_predictor_direction_changed =
        (~branch_metadata_ex.branch_prediction_used) |
        (branch_metadata_ex.branch_predictor_metadata[1] ^ ex_entry.metadata[1]);

    assign tag_update_way = {CONFIG.BP.WAYS{br_results.valid}} & (branch_metadata_ex.branch_predictor_update_way);
    assign target_update_way = {CONFIG.BP.WAYS{branch_predictor_direction_changed}} & tag_update_way;
    ////////////////////////////////////////////////////
    //Target PC if branch flush occured
    assign bp.branch_flush_pc = br_results.target_pc;

    ////////////////////////////////////////////////////
    //RAS support
    assign ras.branch_retired = br_results.valid & br_results.is_branch & branch_metadata_ex.branch_prediction_used;

endmodule
