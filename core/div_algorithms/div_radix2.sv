/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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


module div_radix2
    #(
        parameter DIV_WIDTH = 32
    )
    (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
    );

    logic terminate;

    logic [DIV_WIDTH-1:0] divisor_r;
    logic [DIV_WIDTH:0] new_PR;
    logic [DIV_WIDTH:0] PR;
    logic [DIV_WIDTH-1:0] shift_count;
    logic negative_sub_rst;

    //implementation
    ////////////////////////////////////////////////////
    assign new_PR = PR - {1'b0, divisor_r};
    assign negative_sub_rst = new_PR[DIV_WIDTH];

    //Shift reg for
    always_ff @ (posedge clk) begin
        shift_count <= {shift_count[DIV_WIDTH-2:0], div.start};
    end

    always_ff @ (posedge clk) begin
        if (div.start) begin
            divisor_r <= div.divisor;
            PR <= {(DIV_WIDTH)'(1'b0), div.dividend[DIV_WIDTH-1]};
            div.quotient <= {div.dividend[DIV_WIDTH-2:0], 1'b0};
        end
        else if (~terminate) begin
            PR <= negative_sub_rst ? {PR[DIV_WIDTH-1:0], div.quotient[DIV_WIDTH-1]} : {new_PR[DIV_WIDTH-1:0], div.quotient[DIV_WIDTH-1]};
            div.quotient <= {div.quotient[DIV_WIDTH-2:0], ~negative_sub_rst};
        end
    end

    assign div.remainder = PR[DIV_WIDTH:1];

    always_ff @ (posedge clk) begin
        if (div.start)
            div.divisor_is_zero <= ~div.divisor[0];
        else  if (~terminate)
            div.divisor_is_zero <= div.divisor_is_zero & ~negative_sub_rst;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            terminate <= 0;
        else begin
            if (div.start)
                terminate <= 0;
            if (shift_count[DIV_WIDTH-1])
                terminate <= 1;
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            div.done <= 0;
        else begin
            if (shift_count[DIV_WIDTH-1])
                div.done <= 1;
            else if (div.done)
                div.done <= 0;
        end
    end

endmodule
