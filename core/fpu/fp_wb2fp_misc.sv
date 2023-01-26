/*
 * Copyright © 2019-2023 Yuhui Gao, Lesley Shannon
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
 *             Yuhui Gao <yuhuig@sfu.ca>
 */

//Misc. floating-point units that write-back to floating-point register file
//Sharing 1 write-back port
//FMINMAX, FSIGN_INJ, FCVT_D_W(U)
module fp_wb2fp_misc
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;

(
    input logic clk,
    unit_issue_interface.unit issue,
    input fp_wb2fp_misc_inputs_t fp_wb2fp_misc_inputs,
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
    logic advance;

    ////////////////////////////////////////////////////
    //construct inputs for each unit
    assign fp_i2f_inputs = fp_wb2fp_misc_inputs.fp_i2f_inputs;
    assign fp_minmax_inputs = fp_wb2fp_misc_inputs.fp_minmax_inputs;
    assign fp_sign_inject_inputs = fp_wb2fp_misc_inputs.fp_sign_inject_inputs;

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
        .issue (i2f_issue),
        .fp_i2f_inputs (fp_i2f_inputs),
        .wb (i2f_wb)
    );

    ////////////////////////////////////////////////////
    //MinMax
    fp_minmax fp_minmax_inst(
        .clk (clk),
        .issue (minmax_issue),
        .fp_minmax_inputs (fp_minmax_inputs),
        .wb (minmax_wb)
    );

    ////////////////////////////////////////////////////
    //Sign Injection
    fp_sign_inj fp_sign_inj_inst(
        .clk (clk),
        .issue (sign_inj_issue),
        .fp_sign_inject_inputs (fp_sign_inject_inputs),
        .wb (sign_inj_wb)
    );

    ////////////////////////////////////////////////////
    //Control Signals
    assign advance = wb.ack | ~wb.done;
    assign issue.ready = advance;

    ////////////////////////////////////////////////////
    //Mux Results
    always_ff @(posedge clk) begin
        if (advance) begin
            wb.rm <= fp_wb2fp_misc_inputs.rm;
            wb.done <= issue.new_request;
            wb.id <= issue.id;
            case(fp_wb2fp_misc_inputs.instruction)
                3'b100: begin
                    wb.rd <= i2f_wb.rd;
                    wb.fflags <= i2f_wb.fflags;
                    wb.carry <= i2f_wb.carry;
                    wb.safe <= i2f_wb.safe;
                    wb.hidden <= i2f_wb.hidden;
                    wb.grs <= i2f_wb.grs;
                    wb.clz <= i2f_wb.clz;
                end
                3'b010: begin
                    wb.rd <= minmax_wb.rd;
                    wb.fflags <= minmax_wb.fflags;
                    wb.carry <= minmax_wb.carry;
                    wb.safe <= minmax_wb.safe;
                    wb.hidden <= minmax_wb.hidden;
                    wb.grs <= minmax_wb.grs;
                    wb.clz <= minmax_wb.clz;
                end
                default: begin
                    wb.rd <= sign_inj_wb.rd;
                    wb.fflags <= sign_inj_wb.fflags;
                    wb.carry <= sign_inj_wb.carry;
                    wb.safe <= sign_inj_wb.safe;
                    wb.hidden <= sign_inj_wb.hidden;
                    wb.grs <= sign_inj_wb.grs;
                    wb.clz <= sign_inj_wb.clz;
                end
            endcase
        end
    end

endmodule
