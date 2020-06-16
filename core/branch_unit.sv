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
        output logic branch_flush,

        output logic branch_complete,
        output id_t branch_id,
        input branch_metadata_t branch_metadata_ex,

        output logic potential_branch_exception,
        output logic branch_exception_is_jump,
        output exception_packet_t br_exception,

        //Trace signals
        output logic tr_branch_correct,
        output logic tr_branch_misspredict,
        output logic tr_return_correct,
        output logic tr_return_misspredict
        );

    logic branch_issued_r;

    logic [31:0] jump_base;
    logic result;

    //Branch Predictor
    logic branch_taken;
    logic branch_taken_ex;

    id_t id_ex;
    logic [31:0] new_pc;
    logic [31:0] new_pc_ex;

    logic [31:0] pc_ex;
    logic instruction_is_completing;

    logic jal_jalr_ex;
    ////////////////////////////////////////////////////
    //Implementation
    //Only stall condition is if the following instruction is not valid for pc comparisons.
    //If the next instruction isn't valid, no instruction can be issued anyways, so it
    //is safe to hardcode this to one.
    assign issue.ready = 1;

    //Branch new request is held if the following instruction hasn't arrived at decode/issue yet
    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE(0)) branch_issued_m (
      .clk, .rst,
      .set(issue.new_request),
      .clr(branch_inputs.issue_pc_valid | br_exception.valid),
      .result(branch_issued_r)
    );

    //To determine if the branch was predicted correctly we need to wait until the
    //subsequent instruction has reached the issue stage
    assign instruction_is_completing = branch_issued_r & branch_inputs.issue_pc_valid;

    ////////////////////////////////////////////////////
    //Branch/Jump target determination
    //Branch comparison and final address calculation
    //are performed in the issue stage
    branch_comparator bc (
            .use_signed(branch_inputs.use_signed),
            .less_than(branch_inputs.fn3[2]),
            .a(branch_inputs.rs1),
            .b(branch_inputs.rs2),
            .xor_result(branch_inputs.fn3[0]),
            .result(result)
        );

    assign branch_taken = result | branch_inputs.jalr | branch_inputs.jal;

    assign jump_base = branch_inputs.jalr ? branch_inputs.rs1 : branch_inputs.issue_pc;
    assign new_pc = jump_base + (branch_taken ? 32'(signed'(branch_inputs.pc_offset)) : 4);

    always_ff @(posedge clk) begin
        if (instruction_is_completing | ~branch_issued_r) begin
            branch_taken_ex <= branch_taken;
            new_pc_ex[31:1] <= new_pc[31:1];
            new_pc_ex[0] <= new_pc[0] & ~branch_inputs.jalr;
            id_ex <= issue.id;
            jal_jalr_ex <= branch_inputs.jal | branch_inputs.jalr;
        end
    end

    ////////////////////////////////////////////////////
    //Exception support
    id_t jmp_id;

    generate if (ENABLE_M_MODE) begin
        always_ff @(posedge clk) begin
            if (instruction_is_completing | ~branch_issued_r) begin
                jmp_id <= issue.id;
                branch_exception_is_jump <= (branch_inputs.jal | branch_inputs.jalr);
            end
        end

        assign potential_branch_exception = new_pc[1] & issue.new_request;
        assign br_exception.valid = new_pc_ex[1] & branch_taken_ex & branch_issued_r;
        assign br_exception.code = INST_ADDR_MISSALIGNED;
        assign br_exception.tval = new_pc_ex;
        assign br_exception.id = jmp_id;
    end
    endgenerate

    ////////////////////////////////////////////////////
    //ID Management
    assign branch_complete = instruction_is_completing & (~jal_jalr_ex) & (~br_exception.valid);
    assign branch_id = id_ex;

    ////////////////////////////////////////////////////
    //RAS support
    assign ras.branch_retired = branch_complete & branch_metadata_ex.branch_prediction_used;

    ////////////////////////////////////////////////////
    //Predictor support
    logic is_return;
    logic is_call;
    always_ff @(posedge clk) begin
        if (instruction_is_completing | ~branch_issued_r) begin
            is_return <= branch_inputs.is_return;
            is_call <= branch_inputs.is_call;
            pc_ex <= branch_inputs.issue_pc;
        end
    end

    assign br_results.pc_ex = pc_ex;
    assign br_results.new_pc = new_pc_ex;
    assign br_results.branch_taken = branch_taken_ex;
    assign br_results.branch_ex = instruction_is_completing;
    assign br_results.is_branch_ex = ~jal_jalr_ex;
    assign br_results.is_return_ex = is_return;
    assign br_results.is_call_ex = is_call;

    assign branch_flush = instruction_is_completing && (branch_inputs.issue_pc[31:1] != new_pc_ex[31:1]);

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin
        assign tr_branch_correct = instruction_is_completing & ~is_return & ~branch_flush;
        assign tr_branch_misspredict = instruction_is_completing & ~is_return & branch_flush;
        assign tr_return_correct = instruction_is_completing & is_return & ~branch_flush;
        assign tr_return_misspredict = instruction_is_completing & is_return & branch_flush;
    end
    endgenerate

endmodule
