/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

module branch_unit(
        input logic clk,
        input logic rst,

        func_unit_ex_interface.unit branch_ex,
        input branch_inputs_t branch_inputs,
        branch_table_interface.branch_unit bt,
        ras_interface.branch_unit ras,

        unit_writeback_interface.unit branch_wb
        );

    logic result;
    logic equal;
    logic lessthan;

    logic equal_ex;
    logic lessthan_ex;

    logic [31:0] pc_offset;
    logic [31:0] pc_plus_4;

    logic [2:0] fn3_ex;
    logic [31:0] rd_ex;

    logic [31:0] jump_count;
    logic [31:0] call_count;
    logic [31:0] ret_count;
    logic [31:0] br_count;

    logic signed [32:0] rs1_sext;
    logic signed [32:0] rs2_sext;

    logic jump_ex;
    logic bcomp_ex;
    logic br_taken_dec;

    logic done;
    logic new_jal_jalr_dec;

    logic [31:0] carry_value;
    logic [31:0] select_new_carry;
    logic [31:0] carry;

    assign equal = (branch_inputs.rs1 == branch_inputs.rs2);
    assign rs1_sext = {branch_inputs.rs1[XLEN-1] & branch_inputs.use_signed, branch_inputs.rs1};
    assign rs2_sext = {branch_inputs.rs2[XLEN-1] & branch_inputs.use_signed, branch_inputs.rs2};

    assign lessthan = signed'(rs1_sext) < signed'(rs2_sext);

    always_comb begin
        unique case (fn3_ex) // <-- 010, 011 unused
            BEQ_fn3 : result = equal_ex;
            BNE_fn3 : result = ~equal_ex;
            BLT_fn3 : result = lessthan_ex;
            BGE_fn3 : result = ~lessthan_ex;
            BLTU_fn3 : result = lessthan_ex;
            BGEU_fn3 : result = ~lessthan_ex;
        endcase
    end

    assign  bt.branch_taken = (bcomp_ex & result) | jump_ex;

    always_comb begin
        if (branch_inputs.jal)
            pc_offset = 32'(signed'({branch_inputs.jal_imm, 1'b0}));
        else if (branch_inputs.jalr)
            pc_offset = 32'(signed'(branch_inputs.jalr_imm));
        else
            pc_offset = 32'(signed'({branch_inputs.br_imm, 1'b0}));
    end

    assign bt.prediction_dec = branch_inputs.prediction;


    assign pc_plus_4 = branch_inputs.dec_pc + 4;

    assign bt.branch_ex = branch_ex.new_request;
    always_ff @(posedge clk) begin
        if (branch_ex.new_request_dec)
            fn3_ex <= branch_inputs.fn3;
    end

    always_ff @(posedge clk) begin
        equal_ex <= equal;
        lessthan_ex <= lessthan;
        bt.ex_pc <= branch_inputs.dec_pc;
        bcomp_ex <= branch_inputs.branch_compare;
        jump_ex <= (branch_inputs.jal | branch_inputs.jalr);
        bt.jump_pc <= (branch_inputs.jalr ? branch_inputs.rs1 : branch_inputs.dec_pc) + pc_offset;
        bt.njump_pc <= pc_plus_4;
    end

    //if the destination reg is zero, the result is not "written back" to the register file.
    assign new_jal_jalr_dec = (branch_inputs.jal | branch_inputs.jalr) & ~branch_inputs.rdx0;

    always_ff @(posedge clk) begin
        if (branch_ex.new_request_dec & new_jal_jalr_dec) begin
            rd_ex <= pc_plus_4;
        end
    end

    /*********************************
     *  RAS support
     *********************************/
    generate if (USE_BRANCH_PREDICTOR) begin
            logic rs1_link, rs1_eq_rd, rd_link;
            logic is_call;
            logic is_return;

            assign rs1_link = (branch_inputs.rs1_addr ==?  5'b00?01);
            assign rd_link = (branch_inputs.rd_addr ==?  5'b00?01);
            assign rs1_eq_rd = (branch_inputs.rs1_addr == branch_inputs.rd_addr);

            always_ff @(posedge clk) begin
                is_call <= branch_ex.new_request_dec & ( (branch_inputs.jal & rd_link) |  (branch_inputs.jalr & rd_link) );
                is_return <= branch_ex.new_request_dec & ( (branch_inputs.jalr & ((rs1_link & ~rd_link) | (rs1_link & rd_link & ~rs1_eq_rd))) );
            end

            assign ras.push = is_call;
            assign ras.pop = is_return;
            assign ras.new_addr = rd_ex;
            assign bt.is_return_ex = is_return;
        end
    endgenerate

    /*********************************
     *  Output
     *********************************/
    assign branch_ex.ready = ~done | (done & branch_wb.accepted);
    assign branch_wb.rd = rd_ex;

    always_ff @(posedge clk) begin
        if (rst) begin
            done <= 0;
        end else if (branch_ex.new_request_dec & new_jal_jalr_dec) begin
            done <= 1;
        end else if (branch_wb.accepted) begin
            done <= 0;
        end
    end

    assign branch_wb.done_next_cycle = (done & ~branch_wb.accepted);
    assign branch_wb.done_on_first_cycle = 1;//branch_ex.possible_issue & new_jal_jalr_dec;

    /*********************************************/

    //---------- Simulation counters
    //    always_ff @(posedge clk) begin
    //        if (rst) begin
    //            jump_count <= 0;
    //        end else if (branch_ex.new_request & jump_ex & ~is_call & ~is_return) begin
    //            jump_count <= jump_count+1;
    //        end
    //    end

    //    always_ff @(posedge clk) begin
    //        if (rst) begin
    //            call_count <= 0;
    //        end else if (is_call & branch_ex.new_request) begin
    //            call_count <= call_count+1;
    //        end
    //    end

    //    always_ff @(posedge clk) begin
    //        if (rst) begin
    //            ret_count <= 0;
    //        end else if (is_return & branch_ex.new_request) begin
    //            ret_count <= ret_count+1;
    //        end
    //    end

    //    always_ff @(posedge clk) begin
    //        if (rst) begin
    //            br_count <= 0;
    //        end else if (branch_ex.new_request_dec & branch_inputs.branch_compare) begin
    //            br_count <= br_count+1;
    //        end
    //    end


endmodule
