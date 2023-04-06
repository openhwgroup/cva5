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

module fp_div_sqrt_wrapper
    import fpu_types::*;

(
    input logic                   clk,
    input logic                   rst,
    input fp_div_sqrt_inputs_t    fp_div_sqrt_inputs,
    unit_issue_interface.unit  issue,
    fp_intermediate_wb_interface.unit wb
);

    unit_issue_interface div_issue(), sqrt_issue();
    fp_intermediate_wb_interface div_wb(), sqrt_wb();

    fp_sqrt sqrt(
        .clk (clk),
        .rst (rst),
        .issue (sqrt_issue),
        .fp_div_sqrt_inputs (fp_div_sqrt_inputs),
        .wb (sqrt_wb)
    );

    fp_div div(
        .clk (clk),
        .rst (rst),
        .issue (div_issue),
        .fp_div_sqrt_inputs (fp_div_sqrt_inputs),
        .div_wb (div_wb)
    );

    assign issue.ready = div_issue.ready & sqrt_issue.ready;
    assign div_issue.id = issue.id;
    assign sqrt_issue.id = issue.id;
    assign div_issue.new_request = issue.new_request & ~fp_div_sqrt_inputs.is_sqrt;
    assign sqrt_issue.new_request = issue.new_request & fp_div_sqrt_inputs.is_sqrt;
    assign div_issue.possible_issue = issue.possible_issue;
    assign sqrt_issue.possible_issue = issue.possible_issue;

    always_comb begin
        div_wb.ack = wb.ack & div_wb.done;
        sqrt_wb.ack = wb.ack & sqrt_wb.done;
        if (div_wb.done) begin
            wb.rd = div_wb.rd;
            wb.id = div_wb.id;
            wb.done = div_wb.done;
            wb.fflags = div_wb.fflags;
            wb.hidden = div_wb.hidden;
            wb.grs = div_wb.grs;
            wb.clz = div_wb.clz;
            wb.rm = div_wb.rm;
            wb.expo_overflow = div_wb.expo_overflow;
            wb.subnormal = div_wb.subnormal;
            wb.right_shift = div_wb.right_shift;
            wb.right_shift_amt = div_wb.right_shift_amt;
            wb.d2s = div_wb.d2s;
        end else begin
            wb.rd = sqrt_wb.rd;
            wb.id = sqrt_wb.id;
            wb.done = sqrt_wb.done;
            wb.fflags = sqrt_wb.fflags;
            wb.hidden = sqrt_wb.hidden;
            wb.grs = sqrt_wb.grs;
            wb.clz = sqrt_wb.clz;
            wb.rm = sqrt_wb.rm;
            wb.expo_overflow = sqrt_wb.expo_overflow;
            wb.subnormal = sqrt_wb.subnormal;
            wb.right_shift = sqrt_wb.right_shift;
            wb.right_shift_amt = sqrt_wb.right_shift_amt;
            wb.d2s = sqrt_wb.d2s;
        end
    end
endmodule
