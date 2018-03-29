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

module mul_unit(
        input logic clk,
        input logic rst,
        func_unit_ex_interface.unit mul_ex,
        input mul_inputs_t mul_inputs,
        unit_writeback_interface.unit mul_wb
        );

    logic [65:0] result;
    logic [1:0] mulh;
    logic [1:0] advance;
    logic [1:0] valid;

    logic rs1_signed, rs2_signed;
    logic [33:0] rs1_ext, rs2_ext;
    logic [33:0] rs1_r, rs2_r;

    //implementation
    ////////////////////////////////////////////////////
    assign advance[0] = ~valid[0] | advance[1];
    assign advance[1] = mul_wb.accepted | ~valid[1];

    always_ff @ (posedge clk) begin
        if (rst) begin
            valid <= 2'b00;
        end
        else begin
            if (advance[0])
                valid[0] <=  mul_ex.new_request_dec;
            if (advance[1])
                valid[1] <=  valid[0];
        end
    end

    assign rs1_signed = ~(mul_inputs.op[1:0] == MULHU_fn3[1:0]);
    assign rs2_signed = ~mul_inputs.op[1];

    assign rs1_ext = {mul_inputs.rs1[31] & rs1_signed, mul_inputs.rs1};
    assign rs2_ext = {mul_inputs.rs2[31] & rs2_signed, mul_inputs.rs2};

    //Input and output registered Multiply
    always_ff @ (posedge clk) begin
        if (mul_ex.new_request_dec) begin
            rs1_r <= rs1_ext;
            rs2_r <= rs2_ext;
            mulh[0] <= ~(mul_inputs.op[1:0] == 0);
        end
        if (advance[1]) begin
            result <= (rs1_r) * (rs2_r);
            mulh[1] <= mulh[0];
        end
    end

    //Issue/write-back handshaking
    ////////////////////////////////////////////////////
    assign mul_ex.ready = mul_wb.accepted | ~(&valid);

    assign mul_wb.rd = mulh[1] ? result[63:32] : result[31:0];
    assign mul_wb.done = valid[0] | (valid[1] & ~mul_wb.accepted);
    assign mul_wb.early_done = 0;
    ////////////////////////////////////////////////////

endmodule
