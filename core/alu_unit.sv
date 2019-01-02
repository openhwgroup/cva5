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
        func_unit_ex_interface.unit alu_ex,
        unit_writeback_interface.unit alu_wb,
        input alu_inputs_t alu_inputs
        );

    logic[XLEN:0] add_sub_result;
    logic add_sub_carry_in;
    logic[XLEN-1:0] rshift_result;
    logic[XLEN-1:0] lshift_result;

    logic done;
    logic[XLEN:0] adder_in1;
    logic[XLEN:0] adder_in2;
    logic[XLEN:0] adder_in2_logic;

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
            ALU_ADD_SUB : alu_wb.rd = add_sub_result[XLEN-1:0];
            ALU_SLT : alu_wb.rd = {31'b0, add_sub_result[XLEN]};
            ALU_RSHIFT : alu_wb.rd = rshift_result;
            ALU_LSHIFT : alu_wb.rd = lshift_result;
        endcase
    end

    //Issue/write-back handshaking
    ////////////////////////////////////////////////////
    assign alu_ex.ready =  ~done | (done & alu_wb.accepted);

    always_ff @(posedge clk) begin
        if (rst)
            done <= 0;
        else if (alu_ex.new_request_dec)
            done <= 1;
        else if (alu_wb.accepted)
            done <= 0;
    end

    assign alu_wb.done_next_cycle = 1;//in queue, already done
    assign alu_wb.done_on_first_cycle = 1;//not in queue, always done next cycle
    ////////////////////////////////////////////////////

endmodule
