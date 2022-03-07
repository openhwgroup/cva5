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

module branch_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        unit_issue_interface.unit issue,
        input branch_inputs_t branch_inputs,
        output branch_results_t br_results,
        output logic branch_flush,

        exception_interface.unit exception,

        //Trace signals
        output logic tr_branch_correct,
        output logic tr_branch_misspredict,
        output logic tr_return_correct,
        output logic tr_return_misspredict
    );

    logic branch_issued_r;
    logic result;

    //Branch Predictor
    logic branch_taken;
    logic branch_taken_ex;

    id_t id_ex;
    logic [31:0] jump_pc;
    logic [31:0] new_pc;
    logic [31:0] new_pc_ex;

    logic [31:0] pc_ex;
    logic instruction_is_completing;

    logic branch_complete;
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
      .clr(branch_inputs.issue_pc_valid | exception.valid),
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
        .less_than(branch_inputs.fn3[2]),
        .a(branch_inputs.rs1),
        .b(branch_inputs.rs2),
        .xor_result(branch_inputs.fn3[0]),
        .result(result)
    );
    assign branch_taken = result | branch_inputs.jal_jalr;

    assign jump_pc = (branch_inputs.jalr ? branch_inputs.rs1[31:0] : branch_inputs.issue_pc) + 32'(signed'(branch_inputs.pc_offset));
    assign new_pc = branch_taken ? jump_pc : branch_inputs.pc_p4;

    always_ff @(posedge clk) begin
        if (issue.new_request) begin
            branch_taken_ex <= branch_taken;
            new_pc_ex <= {new_pc[31:1], new_pc[0]  & ~branch_inputs.jalr};
            id_ex <= issue.id;
            jal_jalr_ex <= branch_inputs.jal_jalr;
        end
    end

    ////////////////////////////////////////////////////
    //Exception support
    generate if (CONFIG.INCLUDE_M_MODE) begin : gen_branch_exception
        logic new_exception;

        assign new_exception = new_pc[1] & branch_taken & issue.new_request;
        always_ff @(posedge clk) begin
            if (rst)
                exception.valid <= 0;
            else
                exception.valid <= (exception.valid & ~exception.ack) | new_exception;
        end

        always_ff @(posedge clk) begin
            if (issue.new_request)
                exception.id <= issue.id;
        end
        assign exception.code = INST_ADDR_MISSALIGNED;
        assign exception.tval = new_pc_ex;
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Predictor support
    logic is_return;
    logic is_call;
    always_ff @(posedge clk) begin
        if (issue.possible_issue) begin
            is_return <= branch_inputs.is_return;
            is_call <= branch_inputs.is_call;
            pc_ex <= branch_inputs.issue_pc;
        end
    end

    assign br_results.id = id_ex;
    assign br_results.valid = instruction_is_completing;
    assign br_results.pc = pc_ex;
    assign br_results.target_pc = new_pc_ex;
    assign br_results.branch_taken = branch_taken_ex;
    assign br_results.is_branch = ~jal_jalr_ex;
    assign br_results.is_return = is_return;
    assign br_results.is_call = is_call;

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
