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

module branch_unit(
        input logic clk,
        input logic rst,

        unit_issue_interface.unit issue,
        input branch_inputs_t branch_inputs,
        output branch_results_t br_results,
        ras_interface.branch_unit ras,
        output branch_flush,

        //Trace signals
        output logic tr_branch_correct,
        output logic tr_branch_misspredict,
        output logic tr_return_misspredict
        );

    logic branch_issued_r;

    logic[19:0] jal_imm;
    logic[11:0] jalr_imm;
    logic[11:0] br_imm;

    logic [31:0] pc_offset;
    logic [31:0] jump_base;
    logic [31:0] jump_pc_dec;

    logic result;
    logic result_ex;

    logic [2:0] fn3_ex;
    logic jump_ex;

    //Branch Predictor
    logic branch_taken;
    logic branch_correctly_taken;
    logic branch_correclty_not_taken;
    logic miss_predict;

    logic [31:0] pc_ex;
    logic [31:0] jump_pc;
    logic [31:0] njump_pc;
    logic [1:0] branch_metadata;
    logic branch_prediction_used;
    logic [BRANCH_PREDICTOR_WAYS-1:0] bp_update_way;

    logic instruction_is_completing;

    //RAS
    logic is_call;
    logic is_return;

    //implementation
    ////////////////////////////////////////////////////
    //Only stall condition is if the following instruction is not valid for pc comparisons.
    //If the next instruction isn't valid, no instruction can be issued anyways, so it
    //is safe to hardcode this to one.
    assign issue.ready = 1;

    //Branch new request is held if the following instruction hasn't arrived at decode/issue yet
    always_ff @(posedge clk) begin
        if (rst)
            branch_issued_r <= 0;
        else if (issue.new_request)
            branch_issued_r <= 1;
        else if (branch_inputs.dec_pc_valid)
            branch_issued_r <= 0;
    end

    assign instruction_is_completing = branch_issued_r & branch_inputs.dec_pc_valid;

    branch_comparator bc (
            .use_signed(branch_inputs.use_signed),
            .less_than(branch_inputs.fn3[2]),
            .a(branch_inputs.rs1),
            .b(branch_inputs.rs2),
            .result(result)
        );

    assign branch_taken = (~jump_ex & (result_ex ^ fn3_ex[0])) | jump_ex;

    assign jal_imm = {branch_inputs.instruction[31], branch_inputs.instruction[19:12], branch_inputs.instruction[20], branch_inputs.instruction[30:21]};
    assign jalr_imm = branch_inputs.instruction[31:20];
    assign br_imm = {branch_inputs.instruction[31], branch_inputs.instruction[7], branch_inputs.instruction[30:25], branch_inputs.instruction[11:8]};

    always_comb begin
        unique if (branch_inputs.jalr)
            pc_offset = 32'(signed'(jalr_imm));
        else if (branch_inputs.jal)
            pc_offset = 32'(signed'({jal_imm, 1'b0}));
        else
            pc_offset = 32'(signed'({br_imm, 1'b0}));
    end

    always_comb begin
        if (branch_inputs.jalr)
            jump_base = branch_inputs.rs1;
        else
            jump_base = branch_inputs.dec_pc;
    end

    assign jump_pc_dec = jump_base + pc_offset;

    always_ff @(posedge clk) begin
        if (instruction_is_completing | ~branch_issued_r) begin
            fn3_ex <= branch_inputs.fn3;
            result_ex <= result;
            jump_ex <= (branch_inputs.jal | branch_inputs.jalr);
        end
    end

    //Predictor support
    ////////////////////////////////////////////////////
    always_ff @(posedge clk) begin
        if (instruction_is_completing | ~branch_issued_r) begin
            pc_ex <= branch_inputs.dec_pc;
            jump_pc <= {jump_pc_dec[31:1], 1'b0};
            njump_pc <= branch_inputs.dec_pc + 4;
            branch_metadata <= branch_inputs.branch_metadata;
            branch_prediction_used <= branch_inputs.branch_prediction_used;
            bp_update_way <= branch_inputs.bp_update_way;
        end
    end

    assign br_results.pc_ex = pc_ex;
    assign br_results.jump_pc = jump_pc;
    assign br_results.njump_pc = njump_pc;
    assign br_results.branch_ex_metadata = branch_metadata;

    assign br_results.branch_taken = branch_taken;
    assign br_results.branch_ex = instruction_is_completing;
    assign br_results.is_return_ex = is_return;
    assign br_results.branch_prediction_used = branch_prediction_used;
    assign br_results.bp_update_way = bp_update_way;


    assign branch_correctly_taken = {branch_taken, branch_inputs.dec_pc[31:1]} == {1'b1, jump_pc[31:1]};
    assign branch_correclty_not_taken = {branch_taken, branch_inputs.dec_pc[31:1]} == {1'b0, njump_pc[31:1]};
    assign miss_predict = ~(branch_correctly_taken | branch_correclty_not_taken);

    assign branch_flush = USE_BRANCH_PREDICTOR ?
        instruction_is_completing & miss_predict:
        instruction_is_completing & branch_taken;

    //RAS support
    ////////////////////////////////////////////////////
    generate if (USE_BRANCH_PREDICTOR) begin
            always_ff @(posedge clk) begin
                if (instruction_is_completing | ~branch_issued_r) begin
                    is_call <= branch_inputs.is_call;
                    is_return <= branch_inputs.is_return;
                end
            end

            assign ras.push = instruction_is_completing & is_call;
            assign ras.pop = instruction_is_completing & is_return;
            assign ras.new_addr = njump_pc;
        end
    endgenerate
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin
        assign tr_branch_correct = instruction_is_completing & ~is_return & ~miss_predict;
        assign tr_branch_misspredict = instruction_is_completing & ~is_return & miss_predict;
        assign tr_return_misspredict = instruction_is_completing & is_return & miss_predict;
    end
    endgenerate

endmodule
