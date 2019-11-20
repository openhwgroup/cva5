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
  *             Alec Lu <alec_lu@sfu.ca>
 */


module div_quick_clz_mk2
    (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
    );

    logic running;
    logic terminate;

    logic [div.DATA_WIDTH:0] A0;
    logic [div.DATA_WIDTH:0] A1;
    logic [div.DATA_WIDTH-1:0] A2;

    logic [div.DATA_WIDTH-1:0] new_R;
    logic [div.DATA_WIDTH-1:0] new_Q_bit;
    logic [div.DATA_WIDTH-1:0] new_R2;

    logic [div.DATA_WIDTH-1:0] Q_bit1;
    logic [div.DATA_WIDTH-1:0] Q_bit2;

    logic [div.DATA_WIDTH-1:0] B1;
    logic [div.DATA_WIDTH-1:0] B2;

    localparam CLZ_W = $clog2(div.DATA_WIDTH);
    logic [CLZ_W-1:0] R_CLZ;
    logic [CLZ_W-1:0] B_CLZ;
    logic [CLZ_W-1:0] B_CLZ_r;
    logic [CLZ_W-1:0] CLZ_delta;

    logic [div.DATA_WIDTH-1:0] shiftedB;
    //////////////////////////////////////////

    clz clz_r (.clz_input(div.remainder), .clz(R_CLZ));
    clz clz_b (.clz_input(div.divisor), .clz(B_CLZ));

    always_ff @ (posedge clk) begin
        B_CLZ_r <= B_CLZ;
        shiftedB <= div.divisor << B_CLZ;
    end

    assign CLZ_delta = B_CLZ_r - R_CLZ;

    always_comb begin
        Q_bit1 = 0;
        Q_bit1[CLZ_delta] = 1;
    end
    assign Q_bit2 = {1'b0, Q_bit1[div.DATA_WIDTH-1:1]};

    always_comb begin
        if (A1[div.DATA_WIDTH])
            new_Q_bit = Q_bit2;
        else if (A0[div.DATA_WIDTH] || CLZ_delta == 0)
            new_Q_bit = Q_bit1;
        else
            new_Q_bit = (Q_bit1 | Q_bit2);
    end

    assign B1 = shiftedB >> R_CLZ;
    assign A1 = div.remainder - B1;
    assign B2 = {1'b0, B1[div.DATA_WIDTH-1:1]};
    assign A2 = div.remainder - B2;

    assign A0 = div.remainder - (B1 + B2);

    always_comb begin
        if (A1[div.DATA_WIDTH])
            new_R = A2[div.DATA_WIDTH-1:0];
        else if (A0[div.DATA_WIDTH] || CLZ_delta == 0)
            new_R = A1[div.DATA_WIDTH-1:0];
        else
            new_R = A0[div.DATA_WIDTH-1:0];
    end

    assign div.divisor_is_zero = (B_CLZ == 5'b11111 && ~div.divisor[0]);

    always_ff @ (posedge clk) begin
        if (rst)
            running <= 0;
        else if (div.start & ~div.divisor_is_zero)
            running <= 1;
        else if (terminate)
            running <= 0;
    end

    always_ff @ (posedge clk) begin
        div.done <= (running & terminate) | (div.start & div.divisor_is_zero);
    end

    assign terminate = div.remainder < div.divisor;

    always_ff @ (posedge clk) begin
        if (div.start)
            div.quotient <= div.divisor_is_zero ? '1 : '0;
        else  if (~terminate & running)
            div.quotient <= div.quotient | new_Q_bit;
    end

    initial begin
        div.remainder = 0;
    end
    always @ (posedge clk) begin
        if (div.start)
            div.remainder <= div.dividend;
        else if (~terminate & running)
            div.remainder <= new_R;
    end

endmodule
