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

module branch_table(
        input logic clk,
        input logic rst,
        branch_table_interface.branch_table bt
        );

    parameter BADDR_W = $clog2(BRANCH_TABLE_ENTRIES);
    parameter BTAG_W = 30 - BADDR_W;

    typedef struct packed {
        logic valid;
        logic [BTAG_W-1:0] tag;
        logic use_ras;
    } branch_table_entry_t;

    (* RAM_STYLE="BLOCK" *)
        logic[$bits(branch_table_entry_t)-1:0] branch_table_tag_ram [0:BRANCH_TABLE_ENTRIES-1];
    branch_table_entry_t if_entry;
    branch_table_entry_t ex_entry;
    branch_table_entry_t ex_read;

    (* RAM_STYLE="BLOCK" *)
        logic [31:0] branch_table_addr_ram [0:BRANCH_TABLE_ENTRIES-1];
    logic [31:0] predicted_pc;
    logic [31:0] ex_predicted_pc;

    logic [31:0] miss_predict_br;
    logic [31:0] miss_predict_jal;
    logic [31:0] miss_predict_ret;
    logic [31:0] miss_predict_jalr;

    logic miss_predict;
    logic miss_predict2;

    logic tag_match;
    /////////////////////////////////////////


    initial begin
        for(int i=0; i<BRANCH_TABLE_ENTRIES; i=i+1) begin
            //foreach(branch_table_tag_ram[i]) begin
            branch_table_tag_ram[i] = 0;
            branch_table_addr_ram[i] = RESET_VEC;
        end
    end


    byte_en_BRAM #(.LINES(BRANCH_TABLE_ENTRIES)) branch_tag_ram (
            .clk(clk),
            .addr_a(bt.ex_pc[BADDR_W+1:2]),
            .en_a(bt.branch_ex),
            .be_a('1),
            .data_in_a(ex_entry),
            .data_out_a(),

            .addr_b(bt.next_pc[BADDR_W+1:2]),
            .en_b(bt.new_mem_request),
            .be_b('0),
            .data_in_b('0),
            .data_out_b(if_entry));

    byte_en_BRAM #(.LINES(BRANCH_TABLE_ENTRIES)) branch_address_ram (
            .clk(clk),
            .addr_a(bt.ex_pc[BADDR_W+1:2]),
            .en_a(bt.branch_ex),
            .be_a('1),
            .data_in_a(bt.branch_taken ? bt.jump_pc : bt.njump_pc),
            .data_out_a(),

            .addr_b(bt.next_pc[BADDR_W+1:2]),
            .en_b(bt.new_mem_request),
            .be_b('0),
            .data_in_b('0),
            .data_out_b(predicted_pc));

    //Predict next branch to same location/direction as current
    assign ex_entry.valid = 1;
    assign ex_entry.tag = bt.ex_pc[31:32-BTAG_W];
    assign ex_entry.use_ras = bt.is_return_ex;

    assign miss_predict = bt.branch_ex && ~(
            {bt.branch_taken, bt.dec_pc} == {1'b1, bt.jump_pc} ||
            {bt.branch_taken, bt.dec_pc} == {1'b0, bt.njump_pc});

    assign tag_match = ({if_entry.valid, if_entry.tag} == {1'b1, bt.if_pc[31:32-BTAG_W]});
    assign bt.predicted_pc = predicted_pc;

    generate if (USE_BRANCH_PREDICTOR) begin
            assign bt.use_prediction = tag_match;
            assign bt.flush = miss_predict;
        end else begin
            assign bt.use_prediction = 0;
            assign bt.flush = bt.branch_ex & bt.branch_taken;
        end endgenerate

    assign bt.use_ras = if_entry.use_ras;


    always_ff @(posedge clk) begin
        if (rst) begin
            miss_predict_br <= 0;
        end else if (miss_predict & ~bt.is_return_ex) begin
            miss_predict_br <= miss_predict_br+1;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            miss_predict_ret <= 0;
        end else if (miss_predict & bt.is_return_ex) begin
            miss_predict_ret <= miss_predict_ret+1;
        end
    end

endmodule
