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

module alu_unit(
        input logic clk,
        input logic rst,
        unit_issue_interface.unit issue,
        input alu_inputs_t alu_inputs,
        output unit_writeback_t wb
        );

    logic[XLEN:0] add_sub_result;
    logic add_sub_carry_in;
    logic[XLEN-1:0] rshift_result;
    logic[XLEN-1:0] lshift_result;

    logic[XLEN:0] adder_in1;
    logic[XLEN:0] adder_in2;

    logic[XLEN-1:0] result;
    //implementation
    ////////////////////////////////////////////////////

    //Logic ops put through the adder carry chain to reduce resources
    always_comb begin
        case (alu_inputs.logic_op)
            ALU_LOGIC_XOR : adder_in1 = alu_inputs.in1 ^ alu_inputs.in2;
            ALU_LOGIC_OR : adder_in1 = alu_inputs.in1 | alu_inputs.in2;
            ALU_LOGIC_AND : adder_in1 = alu_inputs.in1 & alu_inputs.in2;
            ALU_LOGIC_ADD : adder_in1 = alu_inputs.in1;
        endcase
        case (alu_inputs.logic_op)
            ALU_LOGIC_XOR : adder_in2 = 0;
            ALU_LOGIC_OR : adder_in2 = 0;
            ALU_LOGIC_AND : adder_in2 = 0;
            ALU_LOGIC_ADD : adder_in2 = alu_inputs.in2 ^ {33{alu_inputs.subtract}};
        endcase
    end

    assign {add_sub_result, add_sub_carry_in} = {adder_in1, alu_inputs.subtract} + {adder_in2, alu_inputs.subtract};

    barrel_shifter shifter (
            .shifter_input(alu_inputs.shifter_in),
            .shift_amount(alu_inputs.in2[4:0]),
            .arith(alu_inputs.arith),
            .lshift(alu_inputs.lshift),
            .shifted_resultr(rshift_result),
            .shifted_resultl(lshift_result)
        );

    //Result mux
    always_comb begin
        case (alu_inputs.op)
            ALU_ADD_SUB : result = add_sub_result[XLEN-1:0];
            ALU_SLT : result = {31'b0, add_sub_result[XLEN]};
            ALU_RSHIFT : result = rshift_result;
            ALU_LSHIFT : result = lshift_result;
        endcase
    end

    ////////////////////////////////////////////////////
    //Output
    assign issue.ready = 1;
    assign wb.rd = result;
    assign wb.done = issue.new_request;
    assign wb.id = issue.instruction_id;

    ////////////////////////////////////////////////////
    //Assertions

endmodule
