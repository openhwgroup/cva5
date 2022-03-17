/*
 * Copyright © 2017-2020 Yuhui Gao,  Lesley Shannon
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
 *             Yuhui Gao <yuhiug@sfu.ca>
 *             */

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

//Misc. floating-point units that write-back to floating-point register file
//Sharing 1 write-back port
//FMINMAX, FSIGN_INJ, FCVT_D_W(U)
module fp_wb2fp_misc (
    input logic clk,
    unit_issue_interface.unit issue,
    input fp_wb2fp_misc_inputs_t fp_wb2fp_misc_inputs,
    input logic flt_minmax,
    fp_unit_writeback_interface.unit wb
);

    unit_issue_interface i2f_issue();
    unit_issue_interface minmax_issue();
    unit_issue_interface sign_inj_issue();
    fp_i2f_inputs_t fp_i2f_inputs;
    fp_minmax_inputs_t fp_minmax_inputs;
    fp_sign_inject_inputs_t fp_sign_inject_inputs;
    fp_unit_writeback_interface i2f_wb();
    fp_unit_writeback_interface minmax_wb();
    fp_unit_writeback_interface sign_inj_wb();

    logic done;
    logic advance;
    id_t id;
    logic [2:0] instruction_r;

    ////////////////////////////////////////////////////
    //construct inputs for each unit
    assign fp_i2f_inputs.i2f_rs1 = fp_wb2fp_misc_inputs.int_rs1;
    assign fp_i2f_inputs.rm = fp_wb2fp_misc_inputs.rm;
    assign fp_i2f_inputs.is_signed = fp_wb2fp_misc_inputs.is_signed;
    
    assign fp_minmax_inputs.rs1 = fp_wb2fp_misc_inputs.rs1;
    assign fp_minmax_inputs.rs2 = fp_wb2fp_misc_inputs.rs2;
    assign fp_minmax_inputs.rs1_hidden_bit = fp_wb2fp_misc_inputs.rs1_hidden_bit;
    assign fp_minmax_inputs.rs2_hidden_bit = fp_wb2fp_misc_inputs.rs2_hidden_bit;
    assign fp_minmax_inputs.rs1_special_case = fp_wb2fp_misc_inputs.rs1_special_case;
    assign fp_minmax_inputs.rs2_special_case = fp_wb2fp_misc_inputs.rs2_special_case;
    assign fp_minmax_inputs.rm = fp_wb2fp_misc_inputs.rm;

    assign fp_sign_inject_inputs.rs1 = fp_wb2fp_misc_inputs.rs1;
    assign fp_sign_inject_inputs.rs1_hidden_bit = fp_wb2fp_misc_inputs.rs1_hidden_bit;
    assign fp_sign_inject_inputs.rs2_sign = fp_wb2fp_misc_inputs.rs2[FLEN-1];
    assign fp_sign_inject_inputs.rm = fp_wb2fp_misc_inputs.rm;

    ////////////////////////////////////////////////////
    //Issue
    always_comb begin
        i2f_issue.new_request = issue.new_request & fp_wb2fp_misc_inputs.instruction[2];
        i2f_issue.id = issue.id; 

        minmax_issue.new_request = issue.new_request & fp_wb2fp_misc_inputs.instruction[1];
        minmax_issue.id = issue.id;

        sign_inj_issue.new_request = issue.new_request & fp_wb2fp_misc_inputs.instruction[0];
        sign_inj_issue.id = issue.id;
    end

    ////////////////////////////////////////////////////
    //I2F
    fp_i2f fp_i2f_inst(
        .clk (clk),
        .advance (advance),
        .issue (i2f_issue),
        .fp_i2f_inputs (fp_i2f_inputs),
        .wb (i2f_wb)
    );

    ////////////////////////////////////////////////////
    //MinMax
    fp_minmax fp_minmax_inst(
        .clk (clk),
        .advance (advance),
        .issue (minmax_issue),
        .flt_minmax (flt_minmax),
        .fp_minmax_inputs (fp_minmax_inputs),
        .wb (minmax_wb)
    );

    ////////////////////////////////////////////////////
    //Sign Injection
    fp_sign_inj fp_sign_inj_inst(
        .clk (clk),
        .advance (advance),
        .issue (sign_inj_issue),
        .fp_sign_inject_inputs (fp_sign_inject_inputs),
        .wb (sign_inj_wb)
    );

    ////////////////////////////////////////////////////
    //Register
    always_ff @ (posedge clk) begin
        if (advance) begin
            instruction_r <= fp_wb2fp_misc_inputs.instruction;
        end
    end

    ////////////////////////////////////////////////////
    //Control Signals
    assign advance = wb.ack | ~wb.done;
    assign issue.ready = advance;
    ////////////////////////////////////////////////////
    //Mux Results
    always_comb begin
        case(instruction_r)
            3'b100: begin
                wb.id = i2f_wb.id;
                wb.done = i2f_wb.done;
                wb.rd = i2f_wb.rd;
                wb.fflags = i2f_wb.fflags;
                wb.rm = i2f_wb.rm;
                wb.carry = i2f_wb.carry;
                wb.safe = i2f_wb.safe;
                wb.hidden = i2f_wb.hidden;
                wb.grs = i2f_wb.grs;
                wb.clz = i2f_wb.clz;
            end
            3'b010: begin
                wb.id = minmax_wb.id;
                wb.done = minmax_wb.done;
                wb.rd = minmax_wb.rd;
                wb.fflags = minmax_wb.fflags;
                wb.rm = minmax_wb.rm;
                wb.carry = minmax_wb.carry;
                wb.safe = minmax_wb.safe;
                wb.hidden = minmax_wb.hidden;
                wb.grs = minmax_wb.grs;
                wb.clz = minmax_wb.clz;
            end
            default: begin
                wb.id = sign_inj_wb.id;
                wb.done = sign_inj_wb.done;
                wb.rd = sign_inj_wb.rd;
                wb.fflags = sign_inj_wb.fflags;
                wb.rm = sign_inj_wb.rm;
                wb.carry = sign_inj_wb.carry;
                wb.safe = sign_inj_wb.safe;
                wb.hidden = sign_inj_wb.hidden;
                wb.grs = sign_inj_wb.grs;
                wb.clz = sign_inj_wb.clz;
            end
        endcase
    end

endmodule

