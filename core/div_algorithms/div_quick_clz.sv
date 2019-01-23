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
               Alec Lu <alec_lu@sfu.ca>
 */


module div_quick_clz
    #(
        parameter C_WIDTH = 32
    )(
        input logic clk,
        input logic rst,
        input logic start,
        input logic ack,
        input logic [C_WIDTH-1:0] A,
        input logic [C_WIDTH-1:0] B,
        output logic [C_WIDTH-1:0] Q,
        output logic [C_WIDTH-1:0] R,
        output logic complete,
        output logic B_is_zero
    );

    logic running;
    logic terminate;

    logic [C_WIDTH-1:0] A_r;
    logic [C_WIDTH:0] A1;
    logic [C_WIDTH-1:0] A2;

    logic [C_WIDTH-1:0] new_R;
    logic [C_WIDTH-1:0] new_Q_bit;

    logic [C_WIDTH-1:0] Q_bit1;
    logic [C_WIDTH-1:0] Q_bit2;

    logic [C_WIDTH-1:0] B1;
    logic [C_WIDTH-1:0] B2;
    logic [C_WIDTH-1:0] B_r;

    localparam CLZ_W = $clog2(C_WIDTH);
    logic [CLZ_W-1:0] R_CLZ;
    logic [CLZ_W-1:0] B_CLZ;
    logic [CLZ_W-1:0] B_CLZ_r;
    logic [CLZ_W-1:0] CLZ_delta;

    logic firstCycle;
    logic [C_WIDTH-1:0] shiftedB;
    //////////////////////////////////////////

    clz clz_r (.clz_input(R), .clz(R_CLZ));
    clz clz_b (.clz_input(B), .clz(B_CLZ));

    always_ff @ (posedge clk) begin
        firstCycle <= start;
        B_CLZ_r <= B_CLZ;
        A_r <= A;
        B_r <= B;
        shiftedB <= B_r << B_CLZ_r;
    end

    assign CLZ_delta = B_CLZ_r - R_CLZ;

    always_comb begin
        Q_bit1 = 0;
        Q_bit1[CLZ_delta] = 1;
    end
    assign Q_bit2 = {1'b0, Q_bit1[C_WIDTH-1:1]};
    assign new_Q_bit = Q | (A1[C_WIDTH] ?  Q_bit2 : Q_bit1);

    assign B1 = shiftedB >> R_CLZ;
    assign A1 = R - B1;
    assign B2 = {1'b0, B1[C_WIDTH-1:1]};
    assign A2 = R - B2;

    assign new_R = A1[C_WIDTH] ? A2[C_WIDTH-1:0] : A1[C_WIDTH-1:0];

    assign B_is_zero = (B_CLZ_r == 5'b11111 && ~B_r[0]);

    always_ff @ (posedge clk) begin
        if (rst)
            running <= 0;
        else if (firstCycle & ~B_is_zero)
            running <= 1;
        else if (terminate)
            running <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            complete <= 0;
        else if (ack)
            complete <= 0;
        else if ((running & terminate) | (firstCycle & B_is_zero))
            complete <= 1;
    end

    assign terminate = ({firstCycle, R} < {1'b0, B_r});

    always_ff @ (posedge clk) begin
        if (firstCycle)
            Q <= B_is_zero ? '1 : '0;
        else  if (~terminate)
            Q <= new_Q_bit;
    end

    initial begin
        R = 0;
    end
    always @ (posedge clk) begin
        if (firstCycle)
            R <= A_r;
        else if (~terminate)
            R <= new_R;
    end

endmodule
