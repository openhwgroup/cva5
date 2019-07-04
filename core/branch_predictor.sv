/*
 * Copyright © 2017, 2018 Eric Matthews,  Lesley Shannon
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

    logic [$bits(branch_table_entry_t)-1:0] tag_ram [BRANCH_TABLE_ENTRIES-1:0];
    branch_table_entry_t if_entry;
    branch_table_entry_t ex_entry;

    logic [31:0] addr_ram [BRANCH_TABLE_ENTRIES-1:0];
    logic [31:0] predicted_pc;

    logic branch_taken;
    logic branch_not_taken;
    logic miss_predict;
    logic tag_match;
    /////////////////////////////////////////

    always_ff @(posedge clk) begin
        if (br_results.branch_ex)
            tag_ram[br_results.pc_ex[2 +: BRANCH_ADDR_W]] <= ex_entry;
    end

    always_ff @(posedge clk) begin
        if (bp.new_mem_request)
            if_entry <= tag_ram[bp.next_pc[2 +: BRANCH_ADDR_W]];
    end

    always_ff @(posedge clk) begin
        if (br_results.branch_ex)
            addr_ram[br_results.pc_ex[2 +: BRANCH_ADDR_W]] <= ex_entry.metadata[1] ? br_results.jump_pc : br_results.njump_pc;
    end

    always_ff @(posedge clk) begin
        if (bp.new_mem_request)
            predicted_pc <= addr_ram[bp.next_pc[2 +: BRANCH_ADDR_W]];
    end

    assign bp.branch_flush_pc = br_results.branch_taken ? br_results.jump_pc : br_results.njump_pc;

    //Predict next branch to same location/direction as current
    assign ex_entry.valid = 1;
    assign ex_entry.tag = br_results.pc_ex[31:32-BTAG_W];
    assign ex_entry.use_ras = br_results.is_return_ex;

    //2-bit saturating counter
    always_comb begin
        case(br_results.branch_ex_metadata)
            2'b00 : ex_entry.metadata = br_results.branch_taken ? 2'b01 : 2'b00;
            2'b01 : ex_entry.metadata = br_results.branch_taken ? 2'b10 : 2'b00;
            2'b10 : ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b01;
            2'b11 : ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b10;
        endcase
    end

    assign tag_match = ({if_entry.valid, if_entry.tag} == {1'b1, bp.if_pc[31:32-BTAG_W]});
    assign bp.predicted_pc = predicted_pc;
    assign bp.metadata = if_entry.metadata;
    assign bp.use_ras = if_entry.use_ras;

    generate if (USE_BRANCH_PREDICTOR) begin
            assign bp.use_prediction = tag_match;
        end else begin
            assign bp.use_prediction = 0;
        end endgenerate

endmodule
