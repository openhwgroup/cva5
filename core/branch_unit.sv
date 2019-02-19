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

module branch_unit(
        input logic clk,
        input logic rst,

        func_unit_ex_interface.unit branch_ex,
        input branch_inputs_t branch_inputs,
        branch_table_interface.branch_unit bt,
        ras_interface.branch_unit ras,

        unit_writeback_interface.unit branch_wb
        );

    logic[19:0] jal_imm;
    logic[11:0] jalr_imm;
    logic[11:0] br_imm;

    logic [31:0] pc_offset;
    logic [31:0] jump_base;
    logic [31:0] jump_pc_dec;

    logic [31:0] pc_plus_4;

    logic signed [32:0] rs1_sext;
    logic signed [32:0] rs2_sext;

    logic result;
    logic equal;
    logic lessthan;

    logic equal_ex;
    logic lessthan_ex;
    logic [2:0] fn3_ex;
    logic [31:0] rd_ex;
    logic jump_ex;

    logic done;
    logic new_jal_jalr_dec_with_rd;

    //Perf monitoring
    logic [31:0] jump_count;
    logic [31:0] call_count;
    logic [31:0] ret_count;
    logic [31:0] br_count;

    //implementation
    ////////////////////////////////////////////////////
    assign equal = (branch_inputs.rs1 == branch_inputs.rs2);
    assign rs1_sext = signed'({branch_inputs.rs1[XLEN-1] & branch_inputs.use_signed, branch_inputs.rs1});
    assign rs2_sext = signed'({branch_inputs.rs2[XLEN-1] & branch_inputs.use_signed, branch_inputs.rs2});

    assign lessthan = rs1_sext < rs2_sext;

    always_comb begin
        case (fn3_ex) // <-- 010, 011 unused
            BEQ_fn3 : result = equal_ex;
            BNE_fn3 : result = ~equal_ex;
            3'b010 : result = equal_ex;
            3'b011 : result = ~equal_ex;
            BLT_fn3 : result = lessthan_ex;
            BGE_fn3 : result = ~lessthan_ex;
            BLTU_fn3 : result = lessthan_ex;
            BGEU_fn3 : result = ~lessthan_ex;
        endcase
    end

    assign  bt.branch_taken = (~jump_ex & result) | jump_ex;


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
    assign pc_plus_4 = branch_inputs.dec_pc + 4;

    assign bt.branch_ex = branch_ex.new_request;

    always_ff @(posedge clk) begin
        fn3_ex <= branch_inputs.fn3;
        equal_ex <= equal;
        lessthan_ex <= lessthan;
        bt.ex_pc <= branch_inputs.dec_pc;
        jump_ex <= (branch_inputs.jal | branch_inputs.jalr);
        bt.jump_pc[31:1] <= jump_pc_dec[31:1];
        bt.jump_pc[0] <= 0;
        bt.njump_pc <= pc_plus_4;
    end

    //if the destination reg is zero, the result is not "written back" to the register file.
    assign new_jal_jalr_dec_with_rd = branch_ex.new_request_dec & branch_inputs.uses_rd;

    always_ff @(posedge clk) begin
        if (branch_ex.possible_issue & branch_inputs.uses_rd) begin
            rd_ex <= pc_plus_4;
        end
    end

    /*********************************
     *  RAS support
     *********************************/
    generate if (USE_BRANCH_PREDICTOR) begin
            logic is_call;
            logic is_return;

            always_ff @(posedge clk) begin
                is_call <= branch_ex.new_request_dec & branch_inputs.is_call;
                is_return <= branch_ex.new_request_dec & branch_inputs.is_return;
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
        end else if (branch_ex.new_request_dec & branch_inputs.uses_rd) begin
            done <= 1;
        end else if (branch_wb.accepted) begin
            done <= 0;
        end
    end

    assign branch_wb.done_next_cycle = branch_ex.possible_issue & branch_inputs.uses_rd;
    assign branch_wb.instruction_id = branch_ex.instruction_id;
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
