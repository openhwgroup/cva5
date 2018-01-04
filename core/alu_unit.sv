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

    logic [XLEN:0] add_sub_result;
    logic [XLEN-1:0] logic_result;

    logic [XLEN-1:0] result;
    logic [XLEN-1:0] result2;

    logic done;

    logic[XLEN:0] add_sub_1;
    logic[XLEN:0] add_sub_2;
    logic[XLEN-1:0] shifter_resultl;
    logic[XLEN-1:0] shifter_resultr;


    assign add_sub_1 = {(alu_inputs.in1[XLEN-1] & ~alu_inputs.sltu), alu_inputs.in1};
    assign add_sub_2 = {(alu_inputs.in2[XLEN-1] & ~alu_inputs.sltu), alu_inputs.in2};

    //Add sub op
    //assign add_sub_result =  alu_inputs.subtract ? (add_sub_1 - add_sub_2) : (add_sub_1 + add_sub_2);
    always_comb begin
        case (alu_inputs.logic_op) // <-- 010, 011 unused
            ALU_XOR : add_sub_result = add_sub_1 ^ add_sub_2;
            ALU_OR : add_sub_result = add_sub_1 | add_sub_2;
            ALU_AND : add_sub_result = add_sub_1 & add_sub_2;
            ALU_ADD_SUB : add_sub_result = alu_inputs.subtract ? add_sub_1 - add_sub_2 : add_sub_1 + add_sub_2;
        endcase
    end

    //alu_logic_ops_and_adder logic_and_adder (
    //        .op_type(alu_inputs.op[1:0]),
    //        .sub(alu_inputs.subtract),
    //        .A(add_sub_1),
    //        .B(add_sub_2),
    //        .result(add_sub_result)
     //   );

    //Barrel Shifter (initial bit flipping occurs in decode/issue stage)
    barrel_shifter shifter (
            .shifter_input(alu_inputs.shifter_in),
            .shift_amount(alu_inputs.in2[4:0]),
            .arith(alu_inputs.arith),
            .lshifted_result(shifter_resultl),
            .rshifted_result(shifter_resultr)
        );

    //Result mux
    always_comb begin
        case (alu_inputs.op)
            ALU_SLT : result = {31'b0, add_sub_result[XLEN]};
            ALU_SHIFTR : result = shifter_resultr;
            ALU_SHIFT : result = shifter_resultl;
            ALU_ADD_SUB : result = add_sub_result[XLEN-1:0];
        endcase
    end


    assign alu_ex.ready =  ~done | (done & alu_wb.accepted);

    assign alu_wb.rd = result;

    always_ff @(posedge clk) begin
        if (rst) begin
            done <= 0;
        end else if (alu_ex.new_request_dec) begin
            done <= 1;
        end else if (alu_wb.accepted) begin
            done <= 0;
        end
    end

    assign alu_wb.done = (done & ~alu_wb.accepted);
    assign alu_wb.early_done = alu_ex.possible_issue;


endmodule
