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
 *             Alec Lu <fla30@sfu.ca>
 */

module quickdiv
        #(
        parameter C_WIDTH = 32

        )
        (
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

    logic running;
    logic terminate;

    logic [C_WIDTH:0] A1;
    logic [C_WIDTH-1:0] A2;

    logic [C_WIDTH-1:0] new_R;
    logic [C_WIDTH-1:0] new_Q_bit;

    logic [C_WIDTH-1:0] Q_bit1;
    logic [C_WIDTH-1:0] Q_bit2;

    logic [C_WIDTH-1:0] B1;
    logic [C_WIDTH-1:0] B2;
    logic [C_WIDTH-1:0] B_r;

    localparam MSB_W = $clog2(C_WIDTH);
    logic [MSB_W-1:0] R_MSB;
    logic [MSB_W-1:0] B_MSB;
    logic [MSB_W-1:0] B_MSB_r;

    logic firstCycle;
    logic [C_WIDTH*2-1:0] shiftedB; 
    logic [C_WIDTH*2-1:0] shiftedQ;
    logic [C_WIDTH*2-1:0] tempB;
    logic [C_WIDTH*2-1:0] tempQ;

    msb msb_r (.msb_input(R), .msb(R_MSB));
    msb msb_b (.msb_input(B), .msb(B_MSB));

    assign new_Q_bit = Q | (A1[C_WIDTH] ?  Q_bit2 : Q_bit1);
    //assign Q_bit1 = 2**MSB_delta_r;
    assign tempQ = shiftedQ << R_MSB;
    assign Q_bit1 = tempQ[63:32];
    assign Q_bit2 = {1'b0, Q_bit1[C_WIDTH-1:1]};

    assign new_R = A1[C_WIDTH] ? A2 : A1[C_WIDTH-1:0];
    //assign B1 = (B_r << MSB_delta_r);
    assign tempB = shiftedB << R_MSB; 
    assign B1 = tempB[63:32];
    assign A1 = R - B1;
    assign B2 = {1'b0,B1[C_WIDTH-1:1]};
    assign A2 = R - B2;

    always_ff @ (posedge clk) begin
        if (firstCycle) begin
            shiftedB <= {B, {C_WIDTH{1'b0}}} >> B_MSB_r;
            shiftedQ <= {32'h00000001, {C_WIDTH{1'b0}}} >> B_MSB_r;
        end
    end

    always_ff @ (posedge clk) begin
        if (rst) begin
            running <= 0;
            complete <= 0;
            firstCycle <= 1;
        end
        else begin
            if (start) begin
                running <= 1;
                complete <= 0;
                firstCycle <= 1;
                B_MSB_r <= B_MSB;
            end
            else if (firstCycle) begin
                firstCycle <= 0;                
            end 
            else if (running & terminate) begin
                running <= 0;
                complete <= 1;
            end
            else if (ack) begin
                running <= 0;
                complete <= 0;
            end
        end
    end

    assign terminate =  (R < B_r);

    always_ff @ (posedge clk) begin
        if (start) begin
            Q <= 0;
            R <= A;
            B_r <= B;
        end
        else  if (~terminate & ~firstCycle) begin
            Q <= new_Q_bit;
            R <= new_R;
        end
    end

endmodule
