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

module branch_predictor (
        input logic clk,
        input logic rst,
        branch_predictor_interface.branch_predictor bp,
        input branch_results_t br_results
        );

    parameter BRANCH_ADDR_W = $clog2(BRANCH_TABLE_ENTRIES);
    parameter BTAG_W = 30 - BRANCH_ADDR_W;

    typedef struct packed {
        logic valid;
        logic [BTAG_W-1:0] tag;
        logic use_ras;
        branch_predictor_metadata_t metadata;
    } branch_table_entry_t;


    branch_table_entry_t [BRANCH_PREDICTOR_WAYS-1:0] if_entry;
    branch_table_entry_t ex_entry;

    logic [31:0] new_jump_addr;
    logic [31:0] predicted_pc [BRANCH_PREDICTOR_WAYS-1:0];

    logic [BRANCH_PREDICTOR_WAYS-1:0] tag_matches;
    logic [BRANCH_PREDICTOR_WAYS-1:0] replacement_way;
    logic [BRANCH_PREDICTOR_WAYS-1:0] update_way;
    logic [$clog2(BRANCH_PREDICTOR_WAYS > 1 ? BRANCH_PREDICTOR_WAYS : 2)-1:0] hit_way;
    logic tag_match;
    /////////////////////////////////////////

    cycler #(BRANCH_PREDICTOR_WAYS) replacement_policy (.*, .en(1'b1), .one_hot(replacement_way));

    genvar i;
    generate if (USE_BRANCH_PREDICTOR)
    for (i=0; i<BRANCH_PREDICTOR_WAYS; i++) begin : branch_tag_banks
        branch_predictor_ram #(.C_DATA_WIDTH($bits(branch_table_entry_t)), .C_DEPTH(BRANCH_TABLE_ENTRIES))
        tag_bank (.*,
            .write_addr(br_results.pc_ex[2 +: BRANCH_ADDR_W]), .write_en(update_way[i]), .write_data(ex_entry),
            .read_addr(bp.next_pc[2 +: BRANCH_ADDR_W]), .read_en(bp.new_mem_request), .read_data(if_entry[i]));
    end
    endgenerate

    generate if (USE_BRANCH_PREDICTOR)
    for (i=0; i<BRANCH_PREDICTOR_WAYS; i++) begin : branch_table_banks
        branch_predictor_ram #(.C_DATA_WIDTH(32), .C_DEPTH(BRANCH_TABLE_ENTRIES))
        addr_table (.*,
            .write_addr(br_results.pc_ex[2 +: BRANCH_ADDR_W]), .write_en(update_way[i]), .write_data(new_jump_addr),
            .read_addr(bp.next_pc[2 +: BRANCH_ADDR_W]), .read_en(bp.new_mem_request), .read_data(predicted_pc[i]));
    end
    endgenerate

    generate if (USE_BRANCH_PREDICTOR)
    for (i=0; i<BRANCH_PREDICTOR_WAYS; i++) begin : branch_hit_detection
            assign tag_matches[i] = ({if_entry[i].valid, if_entry[i].tag} == {1'b1, bp.if_pc[31:32-BTAG_W]});
    end
    endgenerate

    generate if (BRANCH_PREDICTOR_WAYS > 1)
        one_hot_to_integer #(BRANCH_PREDICTOR_WAYS) hit_way_conv (.*, .one_hot(tag_matches), .int_out(hit_way));
    else
        assign hit_way = 0;
    endgenerate
    assign tag_match = |tag_matches;

    assign bp.predicted_pc = predicted_pc[hit_way];
    assign bp.metadata = if_entry[hit_way].metadata;
    assign bp.use_ras = if_entry[hit_way].use_ras;
    assign bp.update_way = tag_matches;

    //Predict next branch to same location/direction as current
    assign ex_entry.valid = 1;
    assign ex_entry.tag = br_results.pc_ex[31:32-BTAG_W];
    assign ex_entry.use_ras = br_results.is_return_ex;

    assign new_jump_addr = ex_entry.metadata[1] ? br_results.jump_pc : br_results.njump_pc;

    //2-bit saturating counter
    always_comb begin
        case(br_results.branch_ex_metadata)
            2'b00 : ex_entry.metadata = br_results.branch_taken ? 2'b01 : 2'b00;
            2'b01 : ex_entry.metadata = br_results.branch_taken ? 2'b10 : 2'b00;
            2'b10 : ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b01;
            2'b11 : ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b10;
        endcase
        if (~br_results.branch_prediction_used)
            ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b00;
    end

    assign update_way = {BRANCH_PREDICTOR_WAYS{br_results.branch_ex}} & (br_results.branch_prediction_used ? br_results.bp_update_way : replacement_way);

    assign bp.branch_flush_pc = br_results.branch_taken ? br_results.jump_pc : br_results.njump_pc;

    generate if (USE_BRANCH_PREDICTOR) begin
            assign bp.use_prediction = tag_match;
        end else begin
            assign bp.use_prediction = 0;
        end endgenerate

endmodule
