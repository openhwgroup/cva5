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

module div_unit

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;

    (
        input logic clk,
        input logic rst,

        input div_inputs_t div_inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );

    logic signed_divop;
    logic negate_quotient;
    logic negate_remainder;
    logic negate_dividend;
    logic negate_divisor;
    logic remainder_op;

    logic [31:0] unsigned_dividend;
    logic [31:0] unsigned_divisor;
    logic [$clog2(32)-1:0] dividend_CLZ;
    logic [$clog2(32)-1:0] divisor_CLZ;

    logic divisor_is_zero;

    typedef struct packed{
        logic remainder_op;
        logic negate_remainder;
        logic negate_quotient;
        logic divisor_is_zero;
        logic reuse_result;
        id_t id;
    } div_attributes_t;

    typedef struct packed{
        logic [XLEN-1:0] unsigned_dividend;
        logic [XLEN-1:0] unsigned_divisor;
        logic [$clog2(32)-1:0] dividend_CLZ;
        logic [$clog2(32)-1:0] divisor_CLZ;
        div_attributes_t attr;
    } div_fifo_inputs_t;

    div_fifo_inputs_t fifo_inputs;
    div_fifo_inputs_t div_op;
    div_attributes_t in_progress_attr;

    unsigned_division_interface #(.DATA_WIDTH(32)) div();

    logic in_progress;
    logic div_done;

    fifo_interface #(.DATA_WIDTH($bits(div_fifo_inputs_t))) input_fifo();
    fifo_interface #(.DATA_WIDTH(XLEN)) wb_fifo();
    ////////////////////////////////////////////////////
    //Implementation
    function logic [31:0] negate_if  (input logic [31:0] a, logic b);
        return ({32{b}} ^ a) + 32'(b);
    endfunction

    ////////////////////////////////////////////////////
    //Input and output sign determination
    assign signed_divop = ~div_inputs.op[0];

    assign negate_dividend = signed_divop & div_inputs.rs1[31];
    assign negate_divisor = signed_divop & div_inputs.rs2[31];

    assign negate_quotient = signed_divop & (div_inputs.rs1[31] ^ div_inputs.rs2[31]);
    assign negate_remainder = signed_divop & (div_inputs.rs1[31]);

    ////////////////////////////////////////////////////
    //Input Processing
    assign unsigned_dividend = negate_if (div_inputs.rs1, negate_dividend);
    assign unsigned_divisor = negate_if (div_inputs.rs2, negate_divisor);

    //Note: If this becomes the critical path, we can use the one's complemented input instead.
    //It will potentially overestimate (only when the input is a negative power-of-two), and
    //the divisor width will need to be increased by one to safely handle the case where the divisor CLZ is overestimated
    clz dividend_clz_block (.clz_input(unsigned_dividend), .clz(dividend_CLZ));
    clz divisor_clz_block (.clz_input(unsigned_divisor), .clz(divisor_CLZ));
    assign divisor_is_zero = (&divisor_CLZ) & ~div_inputs.rs2[0];

    assign fifo_inputs.unsigned_dividend = unsigned_dividend;
    assign fifo_inputs.unsigned_divisor = unsigned_divisor;
    assign fifo_inputs.dividend_CLZ = dividend_CLZ;
    assign fifo_inputs.divisor_CLZ = divisor_CLZ;

    assign fifo_inputs.attr.remainder_op = div_inputs.op[1];
    assign fifo_inputs.attr.negate_remainder = negate_remainder;
    assign fifo_inputs.attr.negate_quotient = negate_quotient;
    assign fifo_inputs.attr.divisor_is_zero = divisor_is_zero;
    assign fifo_inputs.attr.reuse_result = div_inputs.reuse_result;
    assign fifo_inputs.attr.id = issue.id;

    ////////////////////////////////////////////////////
    //Input FIFO
    //Currently just a register (DEPTH=1).  As one div instruction can be in-progress
    //and one in this input "fifo," we can support two in-flight div ops.
    taiga_fifo #(.DATA_WIDTH($bits(div_fifo_inputs_t)), .FIFO_DEPTH(1))
    div_input_fifo (
        .clk    (clk),
        .rst    (rst),
        .fifo   (input_fifo)
    );

    logic div_ready;
    assign div_ready = (~in_progress) | wb.ack;

    assign input_fifo.data_in = fifo_inputs;
    assign input_fifo.push = issue.new_request;
    assign input_fifo.potential_push = issue.possible_issue;
    assign issue.ready = ~input_fifo.full | (~in_progress);
    assign input_fifo.pop = input_fifo.valid & div_ready;
    assign div_op = input_fifo.data_out;

    ////////////////////////////////////////////////////
    //Control Signals
    assign div.start = input_fifo.valid & div_ready & ~div_op.attr.reuse_result;
    assign div_done = div.done | (input_fifo.valid & div_ready & div_op.attr.reuse_result);

    //If more than one cycle, set in_progress so that multiple div.start signals are not sent to the div unit.
    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE('0))
    in_progress_m (
      .clk, .rst,
      .set(input_fifo.pop),
      .clr(wb.ack),
      .result(in_progress)
    );
    always_ff @ (posedge clk) begin
        if (input_fifo.pop)
            in_progress_attr <= div_op.attr;
    end

    ////////////////////////////////////////////////////
    //Div core
    assign div.dividend = div_op.unsigned_dividend;
    assign div.divisor = div_op.unsigned_divisor;
    assign div.dividend_CLZ = div_op.dividend_CLZ;
    assign div.divisor_CLZ = div_op.divisor_CLZ;

    assign div.divisor_is_zero = div_op.attr.divisor_is_zero;
    
    div_core #(.DIV_WIDTH(32)) 
    divider_block (
        .clk(clk),
        .rst(rst),
        .div(div)
    );

    ////////////////////////////////////////////////////
    //Output
    logic negate_result;
    assign negate_result = in_progress_attr.remainder_op ? in_progress_attr.negate_remainder : (~in_progress_attr.divisor_is_zero & in_progress_attr.negate_quotient);
    assign wb.rd = negate_if (in_progress_attr.remainder_op ? div.remainder : ({32{in_progress_attr.divisor_is_zero}} | div.quotient), negate_result);

    always_ff @ (posedge clk) begin
        if (rst)
            wb.done <= 0;
        else
            wb.done <= (wb.done & ~wb.ack) | div_done;
    end

    assign wb.id = in_progress_attr.id;
    ////////////////////////////////////////////////////
    //Assertions

endmodule
