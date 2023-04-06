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

module fp_div
    import fpu_types::*;

(
    input logic                   clk,
    input logic                   rst,
    input fp_div_sqrt_inputs_t    fp_div_sqrt_inputs,
    unit_issue_interface.unit  issue,
    fp_intermediate_wb_interface.unit div_wb
);

    logic                         running;
    logic                         start_algorithm;
    fp_div_sqrt_inputs_t          div_op_attr;

    //input buffer
    fifo_interface #(.DATA_WIDTH($bits(fp_div_sqrt_inputs_t))) input_fifo();
    taiga_fifo #(.DATA_WIDTH($bits(fp_div_sqrt_inputs_t)), .FIFO_DEPTH(1)) fp_div_input_fifo (
        .clk(clk),
        .rst(rst),
        .fifo(input_fifo)
    );

    assign input_fifo.data_in = fp_div_sqrt_inputs;
    assign input_fifo.push = issue.new_request;
    assign input_fifo.potential_push = issue.new_request;
    assign input_fifo.pop = input_fifo.valid & (~running); //fp_wb.done;
    assign issue.ready = ~input_fifo.full | input_fifo.pop;
    assign div_op_attr = input_fifo.data_out;

    assign start_algorithm = input_fifo.valid & (~running);


    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE('0)) in_progress_m (
        .clk, .rst,
        .set(input_fifo.valid & (~running)),
        .clr(div_wb.ack),
        .result(running)
    );

    fp_div_core fp_div_core_inst (
        .clk               (clk),
        .rst               (rst),
        .start_algorithm   (start_algorithm),
        .fp_div_sqrt_inputs(div_op_attr),
        .fp_wb             (div_wb)
    );
endmodule
