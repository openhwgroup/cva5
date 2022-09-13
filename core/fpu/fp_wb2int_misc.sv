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

//Misc. floating-point units that write-back to integer register file
//Sharing 1 write-back port
//FCMP, FCLASS, F2I
module fp_wb2int_misc (
    input logic clk,
    unit_issue_interface.unit issue,
    input fp_wb2int_misc_inputs_t fp_wb2int_misc_inputs,
    unit_writeback_interface.unit wb
);

    fp_f2i_inputs_t fp_f2i_inputs;
    fp_cmp_inputs_t fp_cmp_inputs;
    fp_class_inputs_t fp_class_inputs;
    unit_issue_interface f2i_issue();
    unit_issue_interface cmp_issue();
    unit_issue_interface class_issue();
    unit_writeback_interface f2i_wb();
    unit_writeback_interface cmp_wb();
    unit_writeback_interface class_wb();
    logic [2:0] instruction, instruction_r, instruction_rr;
    logic advance;

    ////////////////////////////////////////////////////
    //construct inputs for each unit
    assign fp_f2i_inputs = fp_wb2int_misc_inputs.fp_f2i_inputs;
    
    assign fp_cmp_inputs = fp_wb2int_misc_inputs.fp_cmp_inputs;
    assign fp_class_inputs.rs1 = fp_wb2int_misc_inputs.rs1;
    assign fp_class_inputs.rs1_hidden_bit = fp_wb2int_misc_inputs.rs1_hidden_bit;
    assign fp_class_inputs.rs1_special_case = fp_wb2int_misc_inputs.rs1_special_case;

    ////////////////////////////////////////////////////
    //Issue Interfaces
    always_comb begin
        //Don't need to AND new_request with the current instruction, as the output mux handles result selection. Keeping for now for sanity check
        f2i_issue.new_request = issue.new_request & fp_wb2int_misc_inputs.instruction[2];
        f2i_issue.id = issue.id;

        cmp_issue.new_request = issue.new_request & fp_wb2int_misc_inputs.instruction[1];
        cmp_issue.id = issue.id;

        class_issue.new_request = issue.new_request & fp_wb2int_misc_inputs.instruction[0];
        class_issue.id = issue.id;
    end

    ////////////////////////////////////////////////////
    //F2I
    fp_f2i fp_f2i_inst(
        .clk (clk),
        .advance (advance),
        .issue (f2i_issue),
        .fp_f2i_inputs (fp_f2i_inputs),
        .wb (f2i_wb)
    );

    ////////////////////////////////////////////////////
    //FCMP
    fp_cmp fp_cmp_inst(
        .clk (clk),
        .advance (advance),
        .issue (cmp_issue),
        .fp_cmp_inputs (fp_cmp_inputs),
        .wb (cmp_wb)
    );

    ////////////////////////////////////////////////////
    //FCLASS
    fp_class fp_class_inst(
        .clk (clk),
        .advance (advance),
        .issue (class_issue),
        .fp_class_inputs (fp_class_inputs),
        .wb (class_wb)
    );

    ////////////////////////////////////////////////////
    //Control Signal
    //TODO: separate the two stages'd advance signal
    assign advance = wb.ack | ~wb.done;
    assign issue.ready = advance;

    ////////////////////////////////////////////////////
    //Registers
    always_ff @ (posedge clk) begin
        if (advance) begin
            instruction <= fp_wb2int_misc_inputs.instruction;
        end
    end

    ////////////////////////////////////////////////////
    //Output
    always_comb begin
        case(instruction)
            3'b100: begin
                wb.done = f2i_wb.done;
                wb.id = f2i_wb.id;
                wb.rd = f2i_wb.rd;
                wb.fflags = f2i_wb.fflags;
            end
            3'b010: begin
                wb.done = cmp_wb.done;
                wb.id = cmp_wb.id;
                wb.rd = cmp_wb.rd;
                wb.fflags = cmp_wb.fflags;
            end
            default: begin
                wb.done = class_wb.done;
                wb.id = class_wb.id;
                wb.rd = class_wb.rd;
                wb.fflags = class_wb.fflags;
            end
        endcase
    end
endmodule   

