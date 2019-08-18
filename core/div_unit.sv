/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

module div_unit
    (
        input logic clk,
        input logic rst,
        func_unit_ex_interface.unit div_ex,
        input div_inputs_t div_inputs,
        unit_writeback_interface.unit div_wb
    );

    logic computation_complete;
    logic div_done;
    logic done;

    logic [31:0] quotient;
    logic [31:0] remainder;

    logic signed_divop;
    logic quotient_signed;
    logic remainder_signed;
    logic dividend_signed;
    logic divisor_signed;

    logic start_algorithm;
    logic in_progress;

    logic [31:0] complementerA;
    logic [31:0] complementerB;

    logic [31:0] result_input;
    logic negateResult;
    logic divisor_zero;

    logic [31:0] div_result_sign_corrected;
    logic [31:0] wb_div_result;
    logic [31:0] rd_bank [MAX_INFLIGHT_COUNT-1:0];

    div_inputs_t stage1;

    fifo_interface #(.DATA_WIDTH($bits(div_inputs_t))) input_fifo();
    fifo_interface #(.DATA_WIDTH(XLEN)) wb_fifo();
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Input FIFO
    taiga_fifo #(.DATA_WIDTH($bits(div_inputs_t)), .FIFO_DEPTH(DIV_INPUT_BUFFER_DEPTH), .FIFO_TYPE(NON_MUXED_INPUT_FIFO)
        ) div_input_fifo (.fifo(input_fifo), .*);

    assign input_fifo.data_in = div_inputs;
    assign input_fifo.push = div_ex.new_request_dec;
    assign div_ex.ready = ~input_fifo.full;
    assign input_fifo.pop = div_done;
    assign stage1 = input_fifo.data_out;

    ////////////////////////////////////////////////////
    //Control Signals
    assign start_algorithm = input_fifo.valid & (~in_progress) & ~stage1.reuse_result;
    assign div_done = computation_complete | (input_fifo.valid & stage1.reuse_result);

    //If more than one cycle, set in_progress so that multiple start_algorithm signals are not sent to the div unit.
    always_ff @(posedge clk) begin
        if (rst)
            in_progress <= 0;
        else if (start_algorithm)
            in_progress <= 1;
        else if (computation_complete)
            in_progress <= 0;
    end

    ////////////////////////////////////////////////////
    //Input and output sign determination
    assign signed_divop = ~stage1.op[0];

    assign dividend_signed = signed_divop & stage1.rs1[31];
    assign divisor_signed = signed_divop & stage1.rs2[31];

    assign quotient_signed = signed_divop & (stage1.rs1[31] ^ stage1.rs2[31]);
    assign remainder_signed = signed_divop & (stage1.rs1[31]);

    ////////////////////////////////////////////////////
    //Input Processing
    assign complementerA = ({32{dividend_signed}} ^ stage1.rs1) + dividend_signed;
    assign complementerB = ({32{divisor_signed}} ^ stage1.rs2) + divisor_signed;

    ////////////////////////////////////////////////////
    //Output muxing
    assign negateResult = stage1.op[1] ? remainder_signed : (~divisor_zero & quotient_signed);
    assign result_input = stage1.op[1] ? remainder : quotient;
    assign wb_div_result = ({32{negateResult}} ^ result_input) + negateResult;

    ////////////////////////////////////////////////////
    //Div core
    div_algorithm #(XLEN) div (.*, .start_algorithm(start_algorithm), .A(complementerA), .B(complementerB), .Q(quotient), .R(remainder), .complete(computation_complete), .ack(computation_complete), .B_is_zero(divisor_zero));

    ////////////////////////////////////////////////////
    //Output bank
    always_ff @(posedge clk) begin
        if (div_done)
            rd_bank[stage1.instruction_id] <= wb_div_result;
    end

    assign div_wb.rd = rd_bank[div_wb.writeback_instruction_id];
    assign div_wb.done_next_cycle = div_done;
    assign div_wb.instruction_id = stage1.instruction_id;

    ////////////////////////////////////////////////////
    //Assertions

endmodule
