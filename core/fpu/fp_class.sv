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

module fp_class
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;
(
    input logic clk,
    input logic advance,
    unit_issue_interface.unit issue,
    input fp_class_inputs_t fp_class_inputs,
    unit_writeback_interface.unit wb
);

    fp_class_inputs_t       fp_class_inputs_r;
    fp_class_inputs_t       fp_class_inputs_rr;

    logic [FLEN-1:0]        rs1;
    logic                   rs1_hidden_bit;
    logic [3:0]             rs1_special_case;

    logic                   rs1_sign;
    logic                   rs1_inf;
    logic                   rs1_subnormal;
    logic                   rs1_zero;
    logic                   neg_inf;
    logic                   neg_normal;
    logic                   neg_subnormal;
    logic                   neg_zero;
    logic                   pos_zero;
    logic                   pos_subnormal;
    logic                   pos_normal;
    logic                   pos_inf;
    logic                   sNaN;
    logic                   qNaN;
    logic                   done, done_r;
    id_t                    id, id_r;

    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Input Processing
    assign rs1 = fp_class_inputs_rr.rs1;
    assign rs1_hidden_bit = fp_class_inputs_rr.rs1_hidden_bit;
    assign rs1_special_case = fp_class_inputs_rr.rs1_special_case;

    assign rs1_sign = rs1[FLEN-1];
    assign rs1_subnormal = ~rs1_hidden_bit;
    assign rs1_inf = rs1_special_case[3];
    assign rs1_zero = rs1_special_case[0];

    assign neg_inf = rs1_sign && rs1_inf;
    assign neg_normal = rs1_sign && !rs1_subnormal;
    assign neg_subnormal = rs1_sign && rs1_subnormal && !rs1_zero;
    assign neg_zero = rs1_sign && rs1_zero;
    assign pos_zero = !rs1_sign && rs1_zero;
    assign pos_subnormal = !rs1_sign && rs1_subnormal && !rs1_zero;
    assign pos_normal = !rs1_sign && !rs1_subnormal;
    assign pos_inf = !rs1_sign && rs1_inf;
    assign sNaN = rs1_special_case[2];//(rs1 == SNAN);
    assign qNaN = rs1_special_case[1];//(rs1 == CANONICAL_NAN);

    ////////////////////////////////////////////////////
    //Registers
    always_ff @ (posedge clk) begin
        if (advance) begin
            fp_class_inputs_r <= fp_class_inputs;
            fp_class_inputs_rr <= fp_class_inputs_r;
            done <= issue.new_request;
            id <= issue.id;
            done_r <= done;
            id_r <= id;
        end
    end

    ////////////////////////////////////////////////////
    //Output
    assign wb.rd = XLEN'({qNaN, sNaN, pos_inf, pos_normal, pos_subnormal, pos_zero, neg_zero, neg_subnormal, neg_normal, neg_inf});
    assign wb.done = done_r;
    assign wb.id = id_r;

endmodule
