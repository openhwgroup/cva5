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
 

module div_quick_radix_4
    (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
    );
    
    logic terminate;
    logic [div.DATA_WIDTH/2-1:0] shift_count;
    
    logic [div.DATA_WIDTH+1:0] PR;
    logic [2:0] new_PR_sign;
    logic [div.DATA_WIDTH+2:0] new_PR_1;
    logic [div.DATA_WIDTH+2:0] new_PR_2;
    logic [div.DATA_WIDTH+2:0] new_PR_3;
    logic [div.DATA_WIDTH+1:0] B_1;
    logic [div.DATA_WIDTH+1:0] B_2;
    logic [div.DATA_WIDTH+1:0] B_3;
    
    logic [div.DATA_WIDTH-1:0] AR_r;
    logic [div.DATA_WIDTH-1:0] Q_temp;
    logic [5:0] shift_num_R;
    logic [6:0] shift_num_R_normalized;
    logic [5:0] shift_num_Q;
    logic [div.DATA_WIDTH*2+1:0] combined;
    logic [div.DATA_WIDTH*2+1:0] combined_normalized;
    logic terminate_early;
    
    localparam CLZ_W = $clog2(div.DATA_WIDTH);
    logic [CLZ_W-1:0] A_CLZ;
    logic [CLZ_W-1:0] B_CLZ;
    logic [CLZ_W-1:0] A_CLZ_r;
    logic [CLZ_W-1:0] B_CLZ_r;
    logic [CLZ_W-1:0] CLZ_delta;
    
    logic firstCycle;    
    logic greaterDivisor;
    logic [div.DATA_WIDTH-1:0] A_shifted;
    logic [div.DATA_WIDTH-1:0] B_shifted;
    logic [div.DATA_WIDTH-1:0] R_shifted;
    logic [div.DATA_WIDTH-1:0] B_shifted_r;
    
    //implementation
    ////////////////////////////////////////////////////
    clz clz_r (.clz_input(div.dividend), .clz(A_CLZ));
    clz clz_b (.clz_input(div.divisor), .clz(B_CLZ));
    
    always_ff @ (posedge clk) begin
        if (rst) begin
          firstCycle <= 0;
          A_CLZ_r <= 0;
          B_CLZ_r <= 0;
          A_shifted <= 0;
          B_shifted <= 0;
        end else begin
          if (div.start) begin
            firstCycle <= 1;
	    A_CLZ_r <= A_CLZ;
	    B_CLZ_r <= B_CLZ;
	    greaterDivisor <= div.divisor > div.dividend;
            A_shifted <= div.dividend << A_CLZ;
            B_shifted <= div.divisor << A_CLZ;
          end else begin
            firstCycle <= 0;
          end 
        end 
    end
    
    assign new_PR_1 = {1'b0, PR} - {1'b0, B_1};
    assign new_PR_2 = {1'b0, PR} - {1'b0, B_2};
    assign new_PR_3 = {1'b0, PR} - {1'b0, B_3};
    assign new_PR_sign = {new_PR_3[div.DATA_WIDTH+2], new_PR_2[div.DATA_WIDTH+2], new_PR_1[div.DATA_WIDTH+2]};
    
    //Shift reg for
    always_ff @ (posedge clk) begin
      if (rst) begin
        shift_count <= 0;
      end else if (firstCycle) begin
        shift_count <= 1;
      end else if (terminate) begin
        shift_count <= 0;
      end else begin
        shift_count <= {shift_count[14:0], firstCycle};
      end  
    end
    
   always_ff @ (posedge clk) begin
        if (firstCycle) begin
           shift_num_R <= 2;
           shift_num_R_normalized <= 2 + {2'b0, A_CLZ_r};
           shift_num_Q <= 32;
        end 
        else if (~terminate & ~terminate_early) begin
            shift_num_R <= shift_num_R + 2;
            shift_num_R_normalized <= shift_num_R_normalized + 2; 
            shift_num_Q <= shift_num_Q - 2;
        end 
    end     
    
    assign combined_normalized = {PR, AR_r} >> shift_num_R_normalized;
    assign div.remainder = combined_normalized[div.DATA_WIDTH-1:0];

    assign combined = {PR, AR_r} >> shift_num_R;
    assign R_shifted = combined[div.DATA_WIDTH-1:0];

    assign terminate_early = ~firstCycle & ((B_shifted_r > R_shifted) | greaterDivisor);
    assign div.quotient = terminate_early ? (Q_temp << shift_num_Q) : Q_temp;
    
    always_ff @ (posedge clk) begin
        if (firstCycle) begin
            PR <= {{(div.DATA_WIDTH){1'b0}}, A_shifted[div.DATA_WIDTH-1:div.DATA_WIDTH-2]};
            Q_temp <= '0;
            AR_r <= {A_shifted[div.DATA_WIDTH-3:0], 2'b00};
            B_shifted_r <= B_shifted;
            B_1 <= {2'b0, B_shifted};           //1xB
            B_2 <= {1'b0, B_shifted, 1'b0};     //2xB
            B_3 <= {1'b0, B_shifted, 1'b0} + {2'b0, B_shifted}; //3xB
        end else if (~terminate & ~terminate_early) begin
            AR_r <= {AR_r[div.DATA_WIDTH-3:0], 2'b00};
            case (new_PR_sign)
                3'b111 : begin
                    PR <= {PR[div.DATA_WIDTH-1:0], AR_r[div.DATA_WIDTH-1:div.DATA_WIDTH-2]};
                    Q_temp <= {div.quotient[div.DATA_WIDTH-3:0], 2'b00};
                end
                3'b110 : begin
                    PR <= {new_PR_1[div.DATA_WIDTH-1:0], AR_r[div.DATA_WIDTH-1:div.DATA_WIDTH-2]};
                    Q_temp <= {div.quotient[div.DATA_WIDTH-3:0], 2'b01};
                end
                3'b100 : begin
                    PR <= {new_PR_2[div.DATA_WIDTH-1:0], AR_r[div.DATA_WIDTH-1:div.DATA_WIDTH-2]};
                    Q_temp <= {div.quotient[div.DATA_WIDTH-3:0], 2'b10};
                end
                default : begin //3'b000 : begin
                    PR <= {new_PR_3[div.DATA_WIDTH-1:0], AR_r[div.DATA_WIDTH-1:div.DATA_WIDTH-2]};
                    Q_temp <= {div.quotient[div.DATA_WIDTH-3:0], 2'b11};
                end
            endcase
        end
    end

    always_ff @ (posedge clk) begin
        if (div.start)
            div.divisor_is_zero <= ~(|div.divisor);
        else  if (~terminate & ~terminate_early)
            div.divisor_is_zero <= div.divisor_is_zero & ~(|new_PR_sign);
    end

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
            div.done <= 0;
        else begin
            if (firstCycle)
                div.done <= 0;
            else if ((shift_count[15] | terminate_early) & ~div.done & ~terminate) 
                div.done <= 1;
            else if (div.done)
                div.done <= 0;
        end
    end

endmodule
