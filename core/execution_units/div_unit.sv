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
    import opcodes::*;

    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

        input logic instruction_issued_with_rd,

        input decode_packet_t decode_stage,
        output logic unit_needed,
        output logic [REGFILE_READ_PORTS-1:0] uses_rs,
        output logic uses_rd,
        
        input issue_packet_t issue_stage,
        input logic issue_stage_ready,
        input rs_addr_t issue_rs_addr [REGFILE_READ_PORTS],
        input logic [31:0] rf [REGFILE_READ_PORTS],

        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );
    common_instruction_t instruction;//rs1_addr, rs2_addr, fn3, fn7, rd_addr, upper/lower opcode
    logic mult_div_op;

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
        id_t id;
    } div_attributes_t;
    div_attributes_t wb_attr;

    typedef struct packed{
        logic [XLEN-1:0] unsigned_dividend;
        logic [XLEN-1:0] unsigned_divisor;
        logic [$clog2(32)-1:0] dividend_CLZ;
        logic [$clog2(32)-1:0] divisor_CLZ;
        logic divisor_is_zero;
        logic reuse_result;
        div_attributes_t attr;
    } div_fifo_inputs_t;

    unsigned_division_interface #(.DATA_WIDTH(32)) div_core();

    logic in_progress;
    logic div_done;

    fifo_interface #(.DATA_TYPE(div_fifo_inputs_t)) input_fifo();

    function logic [31:0] negate_if  (input logic [31:0] a, logic b);
        return ({32{b}} ^ a) + 32'(b);
    endfunction
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Decode
    assign unit_needed = decode_stage.instruction inside {DIV, DIVU, REM, REMU};
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = unit_needed;
        uses_rs[RS2] = unit_needed;
        uses_rd = unit_needed;
    end
    ////////////////////////////////////////////////////
    //Issue

    ////////////////////////////////////////////////////
    //Result resuse (for div/rem pairs)
    rs_addr_t prev_div_rs_addr [2];
    logic [1:0] div_rd_match;
    logic prev_div_result_valid;
    logic div_rs_overwrite;
    logic div_op_reuse;

    always_ff @(posedge clk) begin
        if (issue.new_request)
            prev_div_rs_addr <= issue_rs_addr[RS1:RS2];
    end

    assign div_op_reuse = {prev_div_result_valid, prev_div_rs_addr[RS1], prev_div_rs_addr[RS2]} == {1'b1, issue_rs_addr[RS1],issue_rs_addr[RS2]};

    //Clear if prev div inputs are overwritten by another instruction
    assign div_rd_match[RS1] = (issue_stage.rd_addr == prev_div_rs_addr[RS1]);
    assign div_rd_match[RS2] = (issue_stage.rd_addr == prev_div_rs_addr[RS2]);
    assign div_rs_overwrite = |div_rd_match;

    set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE(0)) prev_div_result_valid_m (
        .clk, .rst,
        .set(issue.new_request & ~((issue_stage.rd_addr == issue_rs_addr[RS1]) | (issue_stage.rd_addr == issue_rs_addr[RS2]))),
        .clr((instruction_issued_with_rd & div_rs_overwrite) | gc.init_clear), //No instructions will be issued while gc.init_clear is asserted
        .result(prev_div_result_valid)
    );

    ////////////////////////////////////////////////////
    //Input and output sign determination
    assign signed_divop = ~ issue_stage.fn3[0];

    assign negate_dividend = signed_divop & rf[RS1][31];
    assign negate_divisor = signed_divop & rf[RS2][31];

    assign negate_quotient = signed_divop & (rf[RS1][31] ^ rf[RS2][31]);
    assign negate_remainder = signed_divop & (rf[RS1][31]);

    ////////////////////////////////////////////////////
    //Input Processing
    assign unsigned_dividend = negate_if (rf[RS1], negate_dividend);
    assign unsigned_divisor = negate_if (rf[RS2], negate_divisor);

    //Note: If this becomes the critical path, we can use the one's complemented input instead.
    //It will potentially overestimate (only when the input is a negative power-of-two), and
    //the divisor width will need to be increased by one to safely handle the case where the divisor CLZ is overestimated
    clz #(.WIDTH(32)) dividend_clz_block (
        .clz_input(unsigned_dividend),
        .clz(dividend_CLZ),
        .zero()
    );
    clz #(.WIDTH(32)) divisor_clz_block (
        .clz_input(unsigned_divisor),
        .clz(divisor_CLZ),
        .zero(divisor_is_zero)
    );

    ////////////////////////////////////////////////////
    //Input FIFO
    //Currently just a register (DEPTH=1).  As one div instruction can be in-progress
    //and one in this input "fifo," we can support two in-flight div ops.
    cva5_fifo #(.DATA_TYPE(div_fifo_inputs_t), .FIFO_DEPTH(1))
    div_input_fifo (
        .clk    (clk),
        .rst    (rst),
        .fifo   (input_fifo)
    );

    logic div_ready;
    assign div_ready = (~in_progress) | wb.ack;

    assign input_fifo.data_in = '{
        unsigned_dividend : unsigned_dividend,
        unsigned_divisor : unsigned_divisor,
        dividend_CLZ : divisor_is_zero ? '0 : dividend_CLZ,
        divisor_CLZ : divisor_CLZ,
        divisor_is_zero : divisor_is_zero,
        reuse_result : div_op_reuse,
        attr : '{
            remainder_op : issue_stage.fn3[1],
            negate_result : (issue_stage.fn3[1] ? negate_remainder : (negate_quotient & ~divisor_is_zero)),
            id : issue.id
        }
    };
    assign input_fifo.push = issue.new_request;
    assign input_fifo.potential_push = issue.possible_issue;
    assign issue.ready = ~input_fifo.full | (~in_progress);
    assign input_fifo.pop = input_fifo.valid & div_ready;

    ////////////////////////////////////////////////////
    //Control Signals
    assign div_core.start = input_fifo.pop & ~input_fifo.data_out.reuse_result;
    assign div_done = div_core.done | (input_fifo.pop & input_fifo.data_out.reuse_result);

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
            wb_attr <= input_fifo.data_out.attr;
    end

    ////////////////////////////////////////////////////
    //Div core
    assign div_core.dividend = input_fifo.data_out.unsigned_dividend;
    assign div_core.divisor = input_fifo.data_out.unsigned_divisor;
    assign div_core.dividend_CLZ = input_fifo.data_out.dividend_CLZ;
    assign div_core.divisor_CLZ = input_fifo.data_out.divisor_CLZ;
    assign div_core.divisor_is_zero = input_fifo.data_out.divisor_is_zero;
    
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
