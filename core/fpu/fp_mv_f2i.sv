/*
 * Copyright © 2023 Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module fp_mv_f2i
    import taiga_config::*;
    import fpu_types::*;
    import riscv_types::*;

(
    input logic clk,
    input logic advance,
    unit_issue_interface.unit issue,
    input fp_mv_f2i_inputs_t fp_mv_f2i_inputs,
    unit_writeback_interface.unit wb
);
    logic done;
    id_t id;
    logic[FLEN_F-1:0] rd;

    always_ff @(posedge clk) begin
        done <= issue.new_request;
        id <= issue.id;
        rd <= fp_mv_f2i_inputs.rs1;
    end

    //This instruction is meant to transfer single precision numbers, so in reduced precision only the single precision bits are used
    assign wb.rd = {{(XLEN-FLEN_F){1'b0}}, rd};
    assign wb.done = done;
    assign wb.id = id;
endmodule
