/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
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
    logic done;

    logic[XLEN:0] add_sub_1;
    logic[XLEN:0] add_sub_2;
    logic[XLEN-1:0] shifter_result;


    assign add_sub_1 = {(alu_inputs.in1[XLEN-1] & ~alu_inputs.sltu), alu_inputs.in1};
    assign add_sub_2 = {(alu_inputs.in2[XLEN-1] & ~alu_inputs.sltu), alu_inputs.in2};

    //Add sub op
    assign add_sub_result = alu_inputs.add ? add_sub_1 + add_sub_2 : add_sub_1 - add_sub_2;

    //Barrel Shifter (initial bit flipping occurs in decode/issue stage)
    barrel_shifter shifter (
            .shifter_input(alu_inputs.shifter_in),
            .shift_amount(alu_inputs.in2[4:0]),
            .arith(alu_inputs.arith),
            .left_shift(alu_inputs.left_shift),
            .shifted_result(shifter_result)
        );

    //Logic ops
    always_comb begin
        unique case (alu_inputs.fn3)// <- only 3 of 8 cases
            XOR_fn3 : logic_result = alu_inputs.in1 ^ alu_inputs.in2;
            OR_fn3 : logic_result = alu_inputs.in1 | alu_inputs.in2;
            AND_fn3 : logic_result = alu_inputs.in1 & alu_inputs.in2;
        endcase
    end

    //Result mux
    always_comb begin
        case (alu_inputs.op)
            ALU_SLT : result = {31'b0, add_sub_result[XLEN]};
            ALU_LOGIC : result = logic_result;
            ALU_SHIFT : result = shifter_result;
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

    assign alu_wb.done = done;
    assign alu_wb.early_done = alu_ex.new_request_dec | (done & ~alu_wb.accepted);


endmodule
