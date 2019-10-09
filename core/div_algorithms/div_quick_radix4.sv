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
 

module div_quick_radix_4
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
    
    logic terminate;
    logic [C_WIDTH/2-1:0] shift_count;
    
    logic [C_WIDTH+1:0] PR;
    logic [2:0] new_PR_sign;
    logic [C_WIDTH+2:0] new_PR_1;
    logic [C_WIDTH+2:0] new_PR_2;
    logic [C_WIDTH+2:0] new_PR_3;
    logic [C_WIDTH+1:0] B_1;
    logic [C_WIDTH+1:0] B_2;
    logic [C_WIDTH+1:0] B_3;
    
    logic [C_WIDTH-1:0] A_r;
    logic [C_WIDTH-1:0] B_r;
    logic [C_WIDTH-1:0] AR_r;
    logic [C_WIDTH-1:0] Q_temp;
    logic [5:0] shift_num_R;
    logic [5:0] shift_num_Q;
    logic [C_WIDTH*2:0] combined;
    logic [C_WIDTH*2:0] combined_normalized;
    logic terminate_early;
    
    localparam CLZ_W = $clog2(C_WIDTH);
    logic [CLZ_W-1:0] A_CLZ;
    logic [CLZ_W-1:0] B_CLZ;
    logic [CLZ_W-1:0] A_CLZ_r;
    logic [CLZ_W-1:0] B_CLZ_r;
    logic [CLZ_W-1:0] CLZ_delta;
    
    logic firstCycle;    
    logic greaterDivisor;
    logic [C_WIDTH-1:0] A_shifted;
    logic [C_WIDTH-1:0] B_shifted;
    logic [C_WIDTH-1:0] R_shifted;
    
    //implementation
    ////////////////////////////////////////////////////
    clz clz_r (.clz_input(A), .clz(A_CLZ));
    clz clz_b (.clz_input(B), .clz(B_CLZ));
    
    always_ff @ (posedge clk) begin
        firstCycle <= start;
        A_CLZ_r <= A_CLZ;
        B_CLZ_r <= B_CLZ;
        A_r <= A;
        B_r <= B;
    end    
    assign A_shifted = A_r << A_CLZ_r;
    assign B_shifted = B_r << A_CLZ_r;
    
    assign new_PR_1 = {1'b0, PR} - {1'b0, B_1};
    assign new_PR_2 = {1'b0, PR} - {1'b0, B_2};
    assign new_PR_3 = {1'b0, PR} - {1'b0, B_3};
    assign new_PR_sign = {new_PR_3[C_WIDTH+2], new_PR_2[C_WIDTH+2], new_PR_1[C_WIDTH+2]};
    
    //Shift reg for
    always_ff @ (posedge clk) begin
       if (firstCycle)
        shift_count <= 32'd1;
    else
        shift_count <= {shift_count[14:0], firstCycle}; 
    end
    
   always_ff @ (posedge clk) begin
        if (firstCycle) begin
           shift_num_R <= 2;
           shift_num_Q <= 32;
        end 
        else if (~terminate & ~terminate_early) begin
            shift_num_R <= shift_num_R + 2;
            shift_num_Q <= shift_num_Q - 2;
        end 
    end     
    
    assign combined_normalized = {PR, AR_r} >> (shift_num_R + A_CLZ_r);
    assign R = combined_normalized[C_WIDTH-1:0];

    assign combined = {PR, AR_r} >> shift_num_R;
    assign R_shifted = combined[C_WIDTH-1:0];

    assign terminate_early = (B_shifted > R_shifted) | greaterDivisor;
    assign Q = terminate_early ? (Q_temp << shift_num_Q) : Q_temp;
    
    always_ff @ (posedge clk) begin
        if (firstCycle) begin
            PR <= {{(C_WIDTH-1){1'b0}}, A_shifted[C_WIDTH-1:C_WIDTH-2]};
            Q_temp <= B_is_zero ? '1 : '0;
            AR_r <= {A_shifted[C_WIDTH-3:0], 2'b00};
            greaterDivisor <= B_r > A_r;
            B_1 <= {2'b0, B_shifted};           //1xB
            B_2 <= {1'b0, B_shifted, 1'b0};     //2xB
            B_3 <= {1'b0, B_shifted, 1'b0} + B_shifted; //3xB
        end else if (~terminate & ~terminate_early) begin
            AR_r <= {AR_r[C_WIDTH-3:0], 2'b00};
            casex (new_PR_sign)
                3'b111 : begin
                    PR <= {PR[C_WIDTH-1:0], AR_r[C_WIDTH-1:C_WIDTH-2]};
                    Q_temp <= {Q[C_WIDTH-3:0], 2'b00};
                end
                3'b110 : begin
                    PR <= {new_PR_1[C_WIDTH-1:0], AR_r[C_WIDTH-1:C_WIDTH-2]};
                    Q_temp <= {Q[C_WIDTH-3:0], 2'b01};
                end
                3'b100 : begin
                    PR <= {new_PR_2[C_WIDTH-1:0], AR_r[C_WIDTH-1:C_WIDTH-2]};
                    Q_temp <= {Q[C_WIDTH-3:0], 2'b10};
                end
                3'b000 : begin
                    PR <= {new_PR_3[C_WIDTH-1:0], AR_r[C_WIDTH-1:C_WIDTH-2]};
                    Q_temp <= {Q[C_WIDTH-3:0], 2'b11};
                end
                default begin
                    PR <= 'x;
                    Q_temp <= 'x;
                end 
            endcase
        end
    end

//    always_ff @ (posedge clk) begin
//        if (firstCycle)
//            B_is_zero <= ~B_r[0];
//        else  if (~terminate)
//            B_is_zero <= B_is_zero & ~(|new_PR_sign);
//    end
    assign B_is_zero = (&B_CLZ_r) & ~B_r[0];

    always_ff @ (posedge clk) begin
        if (rst)
            terminate <= 0;
        else begin
            if (firstCycle)
                terminate <= 0;
            else if (shift_count[15] | terminate_early)
                terminate <= 1;
        end
    end
    
    always_ff @ (posedge clk) begin
        if (rst)
            complete <= 0;
        else begin
            if ((~firstCycle & (shift_count[15] | terminate_early) & ~complete & ~terminate) | (firstCycle & B_is_zero))
                complete <= 1;
            else if (ack)
                complete <= 0;
        end
    end

endmodule