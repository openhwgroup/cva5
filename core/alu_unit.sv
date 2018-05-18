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
    logic[XLEN-1:0] logic_result;
    logic[XLEN-1:0] shifter_result;

    logic done;

    //implementation
    ////////////////////////////////////////////////////
    assign add_sub_result = alu_inputs.subtract ? alu_inputs.in1 - alu_inputs.in2 : alu_inputs.in1 + alu_inputs.in2;
    always_comb begin
        case (alu_inputs.fn3[1:0])
            XOR_fn3 : logic_result = alu_inputs.in1[XLEN-1:0] ^ alu_inputs.in2[XLEN-1:0];
            OR_fn3 : logic_result = alu_inputs.in1[XLEN-1:0] | alu_inputs.in2[XLEN-1:0];
            default : logic_result = alu_inputs.in1[XLEN-1:0] & alu_inputs.in2[XLEN-1:0];
        endcase
    end

    barrel_shifter shifter (
            .shifter_input(alu_inputs.in1[XLEN-1:0]),
            .shift_amount(alu_inputs.in2[4:0]),
            .arith(alu_inputs.arith),
            .lshift(alu_inputs.lshift),
            .shifted_result(shifter_result)
        );

    //Result mux
    always_comb begin
        case (alu_inputs.op)
            ALU_ADD_SUB : alu_wb.rd = add_sub_result[XLEN-1:0];
            ALU_LOGIC : alu_wb.rd = logic_result;
            ALU_SLT : alu_wb.rd = {31'b0, add_sub_result[XLEN]};
            ALU_SHIFT : alu_wb.rd = shifter_result;
        endcase
    end

    //Issue/write-back handshaking
    ////////////////////////////////////////////////////
    assign alu_ex.ready =  ~done | (done & alu_wb.accepted);

    always_ff @(posedge clk) begin
        if (rst) begin
            done <= 0;
        end else if (alu_ex.new_request_dec) begin
            done <= 1;
        end else if (alu_wb.accepted) begin
            done <= 0;
        end
    end

    assign alu_wb.done_next_cycle = 1;//in queue, already done
    assign alu_wb.done_on_first_cycle = 1;//not in queue, always done next cycle
    ////////////////////////////////////////////////////

endmodule
