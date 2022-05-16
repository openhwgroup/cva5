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

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

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
        logic negate_result;
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

    div_fifo_inputs_t issue_fifo_inputs;
    div_fifo_inputs_t div_stage;
    div_attributes_t wb_attr;

    unsigned_division_interface #(.DATA_WIDTH(32)) div_core();

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

    assign issue_fifo_inputs.unsigned_dividend = unsigned_dividend;
    assign issue_fifo_inputs.unsigned_divisor = unsigned_divisor;
    assign issue_fifo_inputs.dividend_CLZ = divisor_is_zero ? '0 : dividend_CLZ;
    assign issue_fifo_inputs.divisor_CLZ = divisor_CLZ;

    assign issue_fifo_inputs.attr.remainder_op = div_inputs.op[1];
    assign issue_fifo_inputs.attr.negate_result = div_inputs.op[1] ? negate_remainder : (negate_quotient & ~divisor_is_zero);
    assign issue_fifo_inputs.attr.divisor_is_zero = divisor_is_zero;
    assign issue_fifo_inputs.attr.reuse_result = div_inputs.reuse_result;
    assign issue_fifo_inputs.attr.id = issue.id;

    ////////////////////////////////////////////////////
    //Input FIFO
    //Currently just a register (DEPTH=1).  As one div instruction can be in-progress
    //and one in this input "fifo," we can support two in-flight div ops.
    cva5_fifo #(.DATA_WIDTH($bits(div_fifo_inputs_t)), .FIFO_DEPTH(1))
    div_input_fifo (
        .clk    (clk),
        .rst    (rst),
        .fifo   (input_fifo)
    );

    logic div_ready;
    assign div_ready = (~in_progress) | wb.ack;

    assign input_fifo.data_in = issue_fifo_inputs;
    assign input_fifo.push = issue.new_request;
    assign input_fifo.potential_push = issue.possible_issue;
    assign issue.ready = ~input_fifo.full | (~in_progress);
    assign input_fifo.pop = input_fifo.valid & div_ready;
    assign div_stage = input_fifo.data_out;

    ////////////////////////////////////////////////////
    //Control Signals
    assign div_core.start = input_fifo.pop & ~div_stage.attr.reuse_result;
    assign div_done = div_core.done | (input_fifo.pop & div_stage.attr.reuse_result);

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
            wb_attr <= div_stage.attr;
    end

    ////////////////////////////////////////////////////
    //Div core
    assign div_core.dividend = div_stage.unsigned_dividend;
    assign div_core.divisor = div_stage.unsigned_divisor;
    assign div_core.dividend_CLZ = div_stage.dividend_CLZ;
    assign div_core.divisor_CLZ = div_stage.divisor_CLZ;
    assign div_core.divisor_is_zero = div_stage.attr.divisor_is_zero;
    
    div_core #(.DIV_WIDTH(32)) 
    divider_block (
        .clk(clk),
        .rst(rst),
        .div(div_core)
    );

    ////////////////////////////////////////////////////
    //Output
    assign wb.rd = negate_if (wb_attr.remainder_op ? div_core.remainder : div_core.quotient, wb_attr.negate_result);

    always_ff @ (posedge clk) begin
        if (rst)
            wb.done <= 0;
        else
            wb.done <= (wb.done & ~wb.ack) | div_done;
    end

    assign wb.id = wb_attr.id;
    ////////////////////////////////////////////////////
    //Assertions

endmodule
