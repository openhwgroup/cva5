/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
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

    parameter ADDR_W = $clog2(BRANCH_TABLE_ENTRIES);
    parameter BTAG_W = 30 - ADDR_W;

    typedef struct packed {
        logic valid;
        logic [BTAG_W-1:0] tag;
        logic prediction;
        logic use_ras;
    } branch_table_entry_t;

    (* RAM_STYLE="BLOCK" *)
    logic[$bits(branch_table_entry_t)-1:0] branch_table_tag_ram [0:BRANCH_TABLE_ENTRIES-1];
    branch_table_entry_t if_entry;
    branch_table_entry_t ex_entry;

    (* RAM_STYLE="BLOCK" *)
    logic [31:0] branch_table_addr_ram [0:BRANCH_TABLE_ENTRIES-1];
    logic [31:0] predicted_pc;

    logic [31:0] miss_predict_br;
    logic [31:0] miss_predict_jal;
    logic [31:0] miss_predict_ret;
    logic [31:0] miss_predict_jalr;


    logic miss_predict;
    logic miss_predict2;

    logic tag_match;

    logic bt_on;

    initial begin
        for(int i=0; i<BRANCH_TABLE_ENTRIES; i=i+1) begin
            //foreach(branch_table_tag_ram[i]) begin
            branch_table_tag_ram[i] = 0;
            branch_table_addr_ram[i] = 0;
        end
    end

    //Tags and prediction
    always_ff @(posedge clk) begin
        if (bt.branch_ex) begin
            branch_table_tag_ram[bt.ex_pc[ADDR_W+1:2]] <= ex_entry;
        end
    end
    always_ff @(posedge clk) begin
        if (bt.new_mem_request)
            if_entry <=  branch_table_tag_ram[bt.next_pc[ADDR_W+1:2]];
    end
    //branch address
    always_ff @(posedge clk) begin
        if (bt.branch_ex) begin
            branch_table_addr_ram[bt.ex_pc[ADDR_W+1:2]] <= ( bt.branch_taken ? bt.jump_pc : bt.njump_pc);
        end
    end
    always_ff @(posedge clk) begin
        if (bt.new_mem_request)
            predicted_pc <=  branch_table_addr_ram[bt.next_pc[ADDR_W+1:2]];
    end
    //Predict next branch to same location/direction as current
    assign ex_entry.valid = 1;
    assign ex_entry.tag = bt.ex_pc[31:32-BTAG_W];
    assign ex_entry.prediction = bt.branch_taken;
    assign ex_entry.use_ras = bt.is_return_ex;


    assign miss_predict = bt.branch_ex && (
            (bt.dec_pc != bt.jump_pc &&  bt.branch_taken) ||
            (bt.dec_pc != bt.njump_pc &&  ~bt.branch_taken));

    assign tag_match = ({if_entry.valid, if_entry.tag} == {(bt.next_pc_valid & bt_on), bt.if_pc[31:32-BTAG_W]});
    assign bt.predicted_pc = predicted_pc;
    assign bt.prediction = if_entry.prediction;

    always_ff @(posedge clk) begin
        if (rst)
            bt_on <= 0;
        else if (bt.branch_ex)
            bt_on <= 1;
    end

    generate if (USE_BRANCH_PREDICTOR) begin
        assign bt.use_prediction = bt_on & tag_match;
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
