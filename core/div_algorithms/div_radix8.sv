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


module div_radix8
        (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
        );

    logic terminate;
    logic [10:0] shift_count;

    logic [div.DATA_WIDTH+2:0] PR;
    logic [div.DATA_WIDTH:0] Q_33;
    logic [6:0] new_PR_sign;

    logic [div.DATA_WIDTH+3:0] new_PR_1;
    logic [div.DATA_WIDTH+3:0] new_PR_2;
    logic [div.DATA_WIDTH+3:0] new_PR_3;
    logic [div.DATA_WIDTH+3:0] new_PR_4;
    logic [div.DATA_WIDTH+3:0] new_PR_5;
    logic [div.DATA_WIDTH+3:0] new_PR_6;
    logic [div.DATA_WIDTH+3:0] new_PR_7;
    logic [div.DATA_WIDTH+2:0] B_1;
    logic [div.DATA_WIDTH+2:0] B_2;
    logic [div.DATA_WIDTH+2:0] B_3;
    logic [div.DATA_WIDTH+2:0] B_4;
    logic [div.DATA_WIDTH+2:0] B_5;
    logic [div.DATA_WIDTH+2:0] B_6;
    logic [div.DATA_WIDTH+2:0] B_7;

    //implementation
    ////////////////////////////////////////////////////
//    assign new_PR_1 = {1'b0, PR} - div.divisor;
//    assign new_PR_2 = {1'b0, PR} - {div.divisor, 1'b0};
//    assign new_PR_3 = {1'b0, PR} - {div.divisor, 1'b0} - div.divisor;
//    assign new_PR_4 = {1'b0, PR} - {div.divisor, 2'b0};
//    assign new_PR_5 = {1'b0, PR} - {div.divisor, 2'b0} - div.divisor;
//    assign new_PR_6 = {1'b0, PR} - {div.divisor, 2'b0} - {div.divisor, 1'b0};
//    assign new_PR_7 = {1'b0, PR} - {div.divisor, 2'b0} - {div.divisor, 1'b0} - div.divisor;
    assign new_PR_1 = {1'b0, PR} - B_1;
    assign new_PR_2 = {1'b0, PR} - B_2;
    assign new_PR_3 = {1'b0, PR} - B_3;
    assign new_PR_4 = {1'b0, PR} - B_4;
    assign new_PR_5 = {1'b0, PR} - B_5;
    assign new_PR_6 = {1'b0, PR} - B_6;
    assign new_PR_7 = {1'b0, PR} - B_7;
    assign new_PR_sign = {new_PR_7[div.DATA_WIDTH+3], new_PR_6[div.DATA_WIDTH+3], new_PR_5[div.DATA_WIDTH+3],
                          new_PR_4[div.DATA_WIDTH+3], new_PR_3[div.DATA_WIDTH+3], new_PR_2[div.DATA_WIDTH+3],
                          new_PR_1[div.DATA_WIDTH+3]};

    //Shift reg for
    always_ff @ (posedge clk) begin
        shift_count <= {shift_count[9:0], div.start};
    end

    always_ff @ (posedge clk) begin
        if (div.start) begin
            PR <= {{(div.DATA_WIDTH){1'b0}}, 1'b0, div.dividend[div.DATA_WIDTH-1:div.DATA_WIDTH-2]};
            Q_33 <= {div.dividend[div.DATA_WIDTH-3:0], 3'b000};
            
            B_1 <= {3'b000, div.divisor};
            B_2 <= {2'b00, div.divisor, 1'b0};
            B_3 <= {2'b00, div.divisor, 1'b0} + {3'b0, div.divisor};
            B_4 <= {1'b0, div.divisor, 2'b00};
            B_5 <= {1'b0, div.divisor, 2'b00} + {3'b0, div.divisor};
            B_6 <= {1'b0, div.divisor, 2'b00} + {2'b00, div.divisor, 1'b0};
            B_7 <= {1'b0, div.divisor, 2'b00} + {2'b00, div.divisor, 1'b0} + {3'b0, div.divisor};
        end
        else if (~terminate) begin
            case (new_PR_sign)
                7'b1111111 : begin
                    PR <= {PR[div.DATA_WIDTH-1:0], Q_33[div.DATA_WIDTH:div.DATA_WIDTH-2]};
                    Q_33 <= {Q_33[div.DATA_WIDTH-3:0], 3'b000};
                end
                7'b1111110 : begin
                    PR <= {new_PR_1[div.DATA_WIDTH-1:0], Q_33[div.DATA_WIDTH:div.DATA_WIDTH-2]};
                    Q_33 <= {Q_33[div.DATA_WIDTH-3:0], 3'b001};
                end
                7'b1111100 : begin
                    PR <= {new_PR_2[div.DATA_WIDTH-1:0], Q_33[div.DATA_WIDTH:div.DATA_WIDTH-2]};
                    Q_33 <= {Q_33[div.DATA_WIDTH-3:0], 3'b010};
                end
                7'b1111000 : begin
                    PR <= {new_PR_3[div.DATA_WIDTH-1:0], Q_33[div.DATA_WIDTH:div.DATA_WIDTH-2]};
                    Q_33 <= {Q_33[div.DATA_WIDTH-3:0], 3'b011};
                end
                7'b1110000 : begin
                    PR <= {new_PR_4[div.DATA_WIDTH-1:0], Q_33[div.DATA_WIDTH:div.DATA_WIDTH-2]};
                    Q_33 <= {Q_33[div.DATA_WIDTH-3:0], 3'b100};
                end
                7'b1100000 : begin
                    PR <= {new_PR_5[div.DATA_WIDTH-1:0], Q_33[div.DATA_WIDTH:div.DATA_WIDTH-2]};
                    Q_33 <= {Q_33[div.DATA_WIDTH-3:0], 3'b101};
                end
                7'b1000000 : begin
                    PR <= {new_PR_6[div.DATA_WIDTH-1:0], Q_33[div.DATA_WIDTH:div.DATA_WIDTH-2]};
                    Q_33 <= {Q_33[div.DATA_WIDTH-3:0], 3'b110};
                end
                default: begin //7'b0000000 : begin
                    PR <= {new_PR_7[div.DATA_WIDTH-1:0], Q_33[div.DATA_WIDTH:div.DATA_WIDTH-2]};
                    Q_33 <= {Q_33[div.DATA_WIDTH-3:0], 3'b111};
                end
            endcase
        end
    end

    assign div.remainder = PR[div.DATA_WIDTH+2:3];
    assign div.quotient = Q_33[div.DATA_WIDTH-1:0];
    
    always_ff @ (posedge clk) begin
        if (div.start)
            div.divisor_is_zero <= ~div.divisor[0];
        else  if (~terminate)
            div.divisor_is_zero <= div.divisor_is_zero & ~(|new_PR_sign);
    end    

    always_ff @ (posedge clk) begin
        if (rst)
            terminate <= 0;
        else begin
            if (div.start)
                terminate <= 0;
            if (shift_count[10])
                terminate <= 1;
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            div.done <= 0;
        else begin
            if (shift_count[10])
                div.done <= 1;
            else if (div.done)
                div.done <= 0;
        end
    end

endmodule
