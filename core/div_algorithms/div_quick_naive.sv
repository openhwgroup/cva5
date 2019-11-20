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


module div_quick_naive
    (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
    );

    logic running;
    logic terminate;

    logic [div.DATA_WIDTH:0] A1;
    logic [div.DATA_WIDTH-1:0] A2;

    logic [div.DATA_WIDTH-1:0] new_R;
    logic [div.DATA_WIDTH-1:0] new_Q_bit;

    logic [div.DATA_WIDTH-1:0] Q_bit1;
    logic [div.DATA_WIDTH-1:0] Q_bit2;

    logic [div.DATA_WIDTH-1:0] B1;
    logic [div.DATA_WIDTH-1:0] B2;

    localparam MSB_W = $clog2(div.DATA_WIDTH);
    logic [MSB_W-1:0] R_MSB;
    logic [MSB_W-1:0] B_MSB;
    logic [MSB_W-1:0] B_MSB_r;
    logic [MSB_W-1:0] MSB_delta;

    msb_naive msb_r (.msb_input(div.remainder), .msb(R_MSB));
    msb_naive msb_b (.msb_input(div.divisor), .msb(B_MSB));
    // msb msb_r (.msb_input(div.remainder), .msb(R_MSB));
    // msb msb_b (.msb_input(div.divisor), .msb(B_MSB));

    assign MSB_delta = R_MSB - B_MSB_r;

    assign Q_bit1 = 2**MSB_delta;
    assign Q_bit2 = {1'b0, Q_bit1[div.DATA_WIDTH-1:1]};
    assign new_Q_bit = div.quotient | (A1[div.DATA_WIDTH] ?  Q_bit2 : Q_bit1);

    assign B1 = div.divisor << MSB_delta;
    assign A1 = div.remainder - B1;
    assign B2 = {1'b0,B1[div.DATA_WIDTH-1:1]};
    assign A2 = div.remainder - B2;

    assign new_R = A1[div.DATA_WIDTH] ? A2 : A1[div.DATA_WIDTH-1:0];

    assign div.divisor_is_zero = (B_MSB == 0 && ~div.divisor[0]);


    always_ff @ (posedge clk) begin
        if (rst)
            running <= 0;
        else if (div.start & ~div.divisor_is_zero)
            running <= 1;
        else if (terminate)
            running <= 0;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            div.done <= 0;
        else if (div.done)
            div.done <= 0;
        else if ((running & terminate) | (div.start & div.divisor_is_zero))
            div.done <= 1;
    end

    assign terminate =  (div.remainder < div.divisor);

    always_ff @ (posedge clk) begin
        B_MSB_r <= B_MSB;
        if (div.start) begin
            div.quotient <= div.divisor_is_zero ? '1 : 0;
            div.remainder <= div.dividend;
        end
        else  if (~terminate & running) begin
            div.quotient <= new_Q_bit;
            div.remainder <= new_R;
        end
    end

endmodule
