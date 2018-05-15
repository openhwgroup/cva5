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

module div_unit(
        input logic clk,
        input logic rst,
        func_unit_ex_interface.unit div_ex,
        input div_inputs_t div_inputs,
        unit_writeback_interface.unit div_wb
        );

    logic div_complete;
    logic div_done;

    logic [31:0] quotient;
    logic [31:0] remainder;

    logic signed_divop;
    logic quotient_signed;
    logic remainder_signed;
    logic dividend_signed;
    logic divisor_signed;

    logic start;
    logic in_progress;
    logic output_ready;
    logic ack;

    logic [31:0] complementerA;
    logic [31:0] complementerB;

    logic [31:0] result_input;
    logic negateResult;

    logic [31:0] div_result_sign_corrected;
    logic [31:0] wb_div_result;

    div_inputs_t stage1;

    fifo_interface #(.DATA_WIDTH($bits(div_inputs_t))) input_fifo();
    fifo_interface #(.DATA_WIDTH(XLEN)) wb_fifo();

    /*********************************
     *  Input FIFO
     *********************************/
    taiga_fifo #(.DATA_WIDTH($bits(div_inputs_t)), .FIFO_DEPTH(DIV_INPUT_BUFFER_DEPTH), .FIFO_TYPE(NON_MUXED_INPUT_FIFO)
            ) div_input_fifo (.fifo(input_fifo), .*);

    assign input_fifo.data_in = div_inputs;
    assign input_fifo.push = div_ex.new_request_dec;
    assign div_ex.ready = ~input_fifo.full;
    assign input_fifo.pop = div_done;
    assign stage1 = input_fifo.data_out;
    /*********************************************/

    assign output_ready = ~div_wb.done_next_cycle | (div_wb.done_next_cycle & div_wb.accepted);
    assign ack = div_complete & output_ready;

    assign start = input_fifo.valid & (~in_progress) & ~(stage1.reuse_result | stage1.div_zero);
    //Abort prevents divider circuit from starting in the case that we are done in one cycle
    assign div_done = (div_complete | (input_fifo.valid & (stage1.reuse_result | stage1.div_zero))) & output_ready;

    //If more than one cycle, set in_progress so that multiple start signals are not sent to the div unit.  Also in progress if an abort occurs but the output FIFO is full
    always_ff @(posedge clk) begin
        if (rst)
            in_progress <= 0;
        else if (start)
            in_progress <= 1;
        else if (ack)
            in_progress <= 0;
    end

    //Input and output sign determination
    assign signed_divop =  ~stage1.op[0];

    assign dividend_signed = signed_divop & stage1.rs1[31];
    assign divisor_signed = signed_divop & stage1.rs2[31];

    assign quotient_signed = signed_divop & (stage1.rs1[31] ^ stage1.rs2[31]);
    assign remainder_signed = signed_divop & (stage1.rs1[31]);
    //************

    assign complementerA = (dividend_signed ? ~stage1.rs1 : stage1.rs1) + dividend_signed;
    assign complementerB = (divisor_signed ? ~stage1.rs2 : stage1.rs2) + divisor_signed;

    assign result_input = stage1.op[1] ? remainder : quotient;
    assign negateResult = (stage1.op[1] ? remainder_signed : quotient_signed);
    assign div_result_sign_corrected = (negateResult ? ~result_input : result_input) + negateResult;
    assign wb_div_result = stage1.div_zero ? (stage1.op[1] ? stage1.rs1 : '1) : div_result_sign_corrected;
    //*************

    //Synthesis time algorithm choice for divider
    generate
        if(USE_VARIABLE_LATENCY_DIV)
            quickdiv #(XLEN) div (.*, .start(start), .A(complementerA), .B(complementerB), .Q(quotient), .R(remainder), .complete(div_complete), .ack(ack));
        else
            normdiv #(XLEN) div (.*, .start(start), .A(complementerA), .B(complementerB), .Q(quotient), .R(remainder), .complete(div_complete), .ack(ack));
    endgenerate

    /*********************************
     *  Output registering/handshaking
     *********************************/
    always_ff @(posedge clk) begin
        if (div_done)
            div_wb.rd <= wb_div_result;
    end

    always_ff @(posedge clk) begin
        if (rst)
            div_wb.done_next_cycle <= 0;
        else if (div_done)
            div_wb.done_next_cycle <= 1;
        else if (div_wb.accepted)
            div_wb.done_next_cycle <= 0;
    end

    assign div_wb.done_on_first_cycle = 0;

endmodule
