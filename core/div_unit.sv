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
import riscv_types::*;
import taiga_types::*;

module div_unit
    (
        input logic clk,
        input logic rst,

        input logic gc_fetch_flush,

        input div_inputs_t div_inputs,
        unit_issue_interface.unit issue,
        output unit_writeback_t wb
    );

    logic signed_divop;
    logic negate_quotient;
    logic negate_remainder;
    logic negate_dividend;
    logic negate_divisor;

    logic [31:0] unsigned_dividend;
    logic [31:0] unsigned_divisor;
    logic remainder_op;

    typedef struct packed{
        logic [XLEN-1:0] unsigned_dividend;
        logic [XLEN-1:0] unsigned_divisor;
        logic remainder_op;
        logic negate_quotient;
        logic negate_remainder;
        logic reuse_result;
        instruction_id_t instruction_id;
    } div_fifo_inputs_t;

    div_fifo_inputs_t fifo_inputs;
    div_fifo_inputs_t div_op;

    unsigned_division_interface #(.DATA_WIDTH(32)) div_core();

    logic in_progress;
    logic div_done;
    logic negate_result;

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

    assign fifo_inputs.unsigned_dividend = unsigned_dividend;
    assign fifo_inputs.unsigned_divisor = unsigned_divisor;
    assign fifo_inputs.remainder_op = div_inputs.op[1];
    assign fifo_inputs.negate_quotient = negate_quotient;
    assign fifo_inputs.negate_remainder = negate_remainder;
    assign fifo_inputs.reuse_result = div_inputs.reuse_result;
    assign fifo_inputs.instruction_id = issue.instruction_id;

    ////////////////////////////////////////////////////
    //Input FIFO
    taiga_fifo #(.DATA_WIDTH($bits(div_fifo_inputs_t)), .FIFO_DEPTH(MAX_INFLIGHT_COUNT))
        div_input_fifo (.fifo(input_fifo), .*);

    assign input_fifo.data_in = fifo_inputs;
    assign input_fifo.push = issue.new_request;
    assign input_fifo.supress_push = gc_fetch_flush;
    assign issue.ready = 1; //As FIFO depth is the same as MAX_INFLIGHT_COUNT
    assign input_fifo.pop = div_done;
    assign div_op = input_fifo.data_out;

    ////////////////////////////////////////////////////
    //Control Signals
    assign div_core.start = input_fifo.valid & (~in_progress) & ~div_op.reuse_result;
    assign div_done = div_core.done | (input_fifo.valid & div_op.reuse_result);

    //If more than one cycle, set in_progress so that multiple div.start signals are not sent to the div unit.
    always_ff @(posedge clk) begin
        if (rst)
            in_progress <= 0;
        else if (div_core.start)
            in_progress <= 1;
        else if (div_core.done)
            in_progress <= 0;
    end

    ////////////////////////////////////////////////////
    //Div core
    assign div_core.dividend = div_op.unsigned_dividend;
    assign div_core.divisor = div_op.unsigned_divisor;
    div_algorithm divider_block (.*, .div(div_core));

    ////////////////////////////////////////////////////
    //Output
    assign negate_result = div_op.remainder_op ? div_op.negate_remainder : (~div_core.divisor_is_zero & div_op.negate_quotient);
    assign wb.rd = negate_if (div_op.remainder_op ? div_core.remainder : ({32{div_core.divisor_is_zero}} | div_core.quotient), negate_result);
    assign wb.done = div_done;
    assign wb.id = div_op.instruction_id;
    ////////////////////////////////////////////////////
    //Assertions

endmodule
