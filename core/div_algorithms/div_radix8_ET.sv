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


module div_radix8_ET
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
        output logic complete
    );

    logic terminate;
    logic terminate_early;
    logic [10:0] shift_count;

    logic [C_WIDTH+2:0] PR;
    logic [C_WIDTH:0] Q_33;
    logic [6:0] new_PR_sign;

    logic [C_WIDTH+3:0] new_PR_1;
    logic [C_WIDTH+3:0] new_PR_2;
    logic [C_WIDTH+3:0] new_PR_3;
    logic [C_WIDTH+3:0] new_PR_4;
    logic [C_WIDTH+3:0] new_PR_5;
    logic [C_WIDTH+3:0] new_PR_6;
    logic [C_WIDTH+3:0] new_PR_7;

    //implementation
    ////////////////////////////////////////////////////
    assign new_PR_1 = {1'b0, PR} - B;
    assign new_PR_2 = {1'b0, PR} - {B, 1'b0};
    assign new_PR_3 = {1'b0, PR} - {B, 1'b0} - B;
    assign new_PR_4 = {1'b0, PR} - {B, 2'b0};
    assign new_PR_5 = {1'b0, PR} - {B, 2'b0} - B;
    assign new_PR_6 = {1'b0, PR} - {B, 2'b0} - {B, 1'b0};
    assign new_PR_7 = {1'b0, PR} - {B, 2'b0} - {B, 1'b0} - B;
    assign new_PR_sign = {new_PR_7[C_WIDTH+3], new_PR_6[C_WIDTH+3], new_PR_5[C_WIDTH+3],
                          new_PR_4[C_WIDTH+3], new_PR_3[C_WIDTH+3], new_PR_2[C_WIDTH+3],
                          new_PR_1[C_WIDTH+3]};

    //Shift reg for
    always_ff @ (posedge clk) begin
        shift_count <= {shift_count[9:0], start & ~terminate_early};
    end

    assign terminate_early = B > A;

    always_ff @ (posedge clk) begin
        if (start) begin
            if (terminate_early) begin
                PR <= {A, 3'b000};
                Q_33 <= '0;
            end else begin
                PR <= {{(C_WIDTH){1'b0}}, 1'b0, A[C_WIDTH-1:C_WIDTH-2]};
                Q_33 <= {A[C_WIDTH-3:0], 3'b000};                
            end
        end
        else if (~terminate) begin
            casex (new_PR_sign)
                7'b1111111 : begin
                    PR <= {PR[C_WIDTH-1:0], Q_33[C_WIDTH:C_WIDTH-2]};
                    Q_33 <= {Q_33[C_WIDTH-3:0], 3'b000};
                end
                7'b1111110 : begin
                    PR <= {new_PR_1[C_WIDTH-1:0], Q_33[C_WIDTH:C_WIDTH-2]};
                    Q_33 <= {Q_33[C_WIDTH-3:0], 3'b001};
                end
                7'b1111100 : begin
                    PR <= {new_PR_2[C_WIDTH-1:0], Q_33[C_WIDTH:C_WIDTH-2]};
                    Q_33 <= {Q_33[C_WIDTH-3:0], 3'b010};
                end
                7'b1111000 : begin
                    PR <= {new_PR_3[C_WIDTH-1:0], Q_33[C_WIDTH:C_WIDTH-2]};
                    Q_33 <= {Q_33[C_WIDTH-3:0], 3'b011};
                end
                7'b1110000 : begin
                    PR <= {new_PR_4[C_WIDTH-1:0], Q_33[C_WIDTH:C_WIDTH-2]};
                    Q_33 <= {Q_33[C_WIDTH-3:0], 3'b100};
                end
                7'b1100000 : begin
                    PR <= {new_PR_5[C_WIDTH-1:0], Q_33[C_WIDTH:C_WIDTH-2]};
                    Q_33 <= {Q_33[C_WIDTH-3:0], 3'b101};
                end
                7'b1000000 : begin
                    PR <= {new_PR_6[C_WIDTH-1:0], Q_33[C_WIDTH:C_WIDTH-2]};
                    Q_33 <= {Q_33[C_WIDTH-3:0], 3'b110};
                end
                7'b0000000 : begin
                    PR <= {new_PR_7[C_WIDTH-1:0], Q_33[C_WIDTH:C_WIDTH-2]};
                    Q_33 <= {Q_33[C_WIDTH-3:0], 3'b111};
                end
                default begin
                    PR <= 'x;
                    Q_33 <= 'x;
                end
            endcase
        end
    end

    assign R = PR[C_WIDTH+2:3];
    assign Q = Q_33[C_WIDTH-1:0];

    always_ff @ (posedge clk) begin
        if (rst)
            terminate <= 0;
        else begin
            if (start)
                if (terminate_early) begin
                    terminate <= 1;
                end else begin
                    terminate <= 0;
                end
            if (shift_count[10])
                terminate <= 1;
        end
    end
    
    always_ff @ (posedge clk) begin
        if (rst)
            complete <= 0;
        else begin
            if (ack)
                complete <= 0;
            else if ((~start & (shift_count[10])) | (start & terminate_early))
                complete <= 1;
        end
    end

endmodule