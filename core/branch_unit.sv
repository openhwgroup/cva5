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
        input logic [31:0] dec_pc_plus_4,//Sourced from ALU datapath on jal/jalr
        output branch_results_t br_results,
        ras_interface.branch_unit ras,
        output logic branch_flush,

        output logic branch_complete,
        output id_t branch_id,

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
    logic result_ex;

    logic [2:0] fn3_ex;
    logic jump_ex;

    //Branch Predictor
    logic branch_taken;
    logic branch_taken_ex;
    logic branch_correctly_taken;
    logic branch_correclty_not_taken;
    logic miss_predict;

    id_t id_ex;
    logic [31:0] new_pc;
    logic [31:0] new_pc_ex;

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
    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE(0)) branch_issued_m (
      .clk, .rst,
      .set(issue.new_request),
      .clr(branch_inputs.dec_pc_valid | br_exception.valid),
      .result(branch_issued_r)
    );

    assign instruction_is_completing = branch_issued_r & branch_inputs.dec_pc_valid;

    branch_comparator bc (
            .use_signed(branch_inputs.use_signed),
            .less_than(branch_inputs.fn3[2]),
            .a(branch_inputs.rs1),
            .b(branch_inputs.rs2),
            .xor_result(branch_inputs.fn3[0]),
            .result(result)
        );

    assign branch_taken = result | branch_inputs.jalr | branch_inputs.jal;

    always_comb begin
        if (branch_inputs.jalr)
            jump_base = branch_inputs.rs1;
        else
            jump_base = branch_inputs.dec_pc;
    end

    assign new_pc = jump_base + (branch_taken ? 32'(signed'(branch_inputs.pc_offset)) : 4);


    always_ff @(posedge clk) begin
        if (instruction_is_completing | ~branch_issued_r) begin
            branch_taken_ex <= branch_taken;
            new_pc_ex <= new_pc;
            fn3_ex <= branch_inputs.fn3;
            result_ex <= result;
            jump_ex <= (branch_inputs.jal | branch_inputs.jalr);
            id_ex <= issue.id;
        end
    end

    ////////////////////////////////////////////////////
    //Exception support
    instruction_id_t jmp_instruction_id;

    generate if (ENABLE_M_MODE) begin
        always_ff @(posedge clk) begin
            if (instruction_is_completing | ~branch_issued_r)
                jmp_instruction_id <= issue.instruction_id;
        end

        assign potential_branch_exception = 0;// jump_pc_dec[1] & issue.new_request;

        assign br_exception.valid = 0;//(jump_pc[1] & branch_taken) & branch_issued_r;
        assign br_exception.code = INST_ADDR_MISSALIGNED;
        assign br_exception.pc = pc_ex;
        assign br_exception.tval = new_pc_ex;
        assign br_exception.id = jmp_instruction_id;

        assign branch_exception_is_jump = (branch_inputs.jal | branch_inputs.jalr);
    end
    endgenerate

    ////////////////////////////////////////////////////
    //ID Management
    assign branch_complete = instruction_is_completing;
    assign branch_id = id_ex;

    ////////////////////////////////////////////////////
    //Predictor support
    always_ff @(posedge clk) begin
        if (issue.new_request)
            njump_pc <= dec_pc_plus_4;
    end
    always_ff @(posedge clk) begin
        if (instruction_is_completing | ~branch_issued_r) begin
            pc_ex <= branch_inputs.dec_pc;
        end
    end

    assign br_results.pc_ex = pc_ex;
    assign br_results.new_pc = new_pc_ex;
    assign br_results.branch_taken = branch_taken_ex;
    assign br_results.branch_ex = instruction_is_completing;
    assign br_results.is_return_ex = is_return;

    assign branch_flush = instruction_is_completing && (branch_inputs.dec_pc[31:1] != new_pc_ex[31:1]);

    ////////////////////////////////////////////////////
    //RAS support
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
        assign tr_branch_correct = instruction_is_completing & ~is_return & ~branch_flush;
        assign tr_branch_misspredict = instruction_is_completing & ~is_return & branch_flush;
        assign tr_return_correct = instruction_is_completing & is_return & ~branch_flush;
        assign tr_return_misspredict = instruction_is_completing & is_return & branch_flush;
    end
    endgenerate

endmodule
