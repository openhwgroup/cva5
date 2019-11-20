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
 

module div_radix4_ET_full
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
    
    logic [div.DATA_WIDTH-1:0] B_r;
    logic [div.DATA_WIDTH-1:0] AR_r;
    logic [div.DATA_WIDTH-1:0] Q_temp;
    logic [5:0] shift_num_R;
    logic [5:0] shift_num_Q;
    logic [div.DATA_WIDTH*2:0] combined;
    logic terminate_early;    
    
    //implementation
    ////////////////////////////////////////////////////
    assign new_PR_1 = {1'b0, PR} - {1'b0, B_1};
    assign new_PR_2 = {1'b0, PR} - {1'b0, B_2};
    assign new_PR_3 = {1'b0, PR} - {1'b0, B_3};
    assign new_PR_sign = {new_PR_3[div.DATA_WIDTH+2], new_PR_2[div.DATA_WIDTH+2], new_PR_1[div.DATA_WIDTH+2]};
    
    //Shift reg for
    always_ff @ (posedge clk) begin
       if (div.start)
        shift_count <= 1;
    else
        shift_count <= {shift_count[14:0], div.start};
    end
    
   always_ff @ (posedge clk) begin
        if (div.start) begin
           shift_num_R <= 2;
           shift_num_Q <= 32;
        end 
        else if (~terminate & ~terminate_early) begin
            shift_num_R <= shift_num_R + 2;
            shift_num_Q <= shift_num_Q - 2;
        end 
    end     
    
    assign combined = {PR[div.DATA_WIDTH:0], AR_r} >> shift_num_R;
    assign div.remainder = combined[div.DATA_WIDTH-1:0];
    assign terminate_early = B_r > div.remainder;
    assign div.quotient = terminate_early ? (Q_temp << shift_num_Q) : Q_temp;
    
    always_ff @ (posedge clk) begin
        if (div.start) begin
            PR <= {{(div.DATA_WIDTH){1'b0}}, div.dividend[div.DATA_WIDTH-1:div.DATA_WIDTH-2]};
            Q_temp <= '0;
            AR_r <= {div.dividend[div.DATA_WIDTH-3:0], 2'b00};
            B_r <= div.divisor;
            B_1 <= {2'b0, div.divisor};           //1xB
            B_2 <= {1'b0, div.divisor, 1'b0};     //2xB
            B_3 <= {1'b0, div.divisor, 1'b0} + {2'b0, div.divisor}; //3xB
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
                default: begin //3'b000 : begin
                    PR <= {new_PR_3[div.DATA_WIDTH-1:0], AR_r[div.DATA_WIDTH-1:div.DATA_WIDTH-2]};
                    Q_temp <= {div.quotient[div.DATA_WIDTH-3:0], 2'b11};
                end
            endcase
        end
    end

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
            else if (shift_count[15] | terminate_early)
                terminate <= 1;
        end
    end
    
    always_ff @ (posedge clk) begin
        if (rst)
            div.done <= 0;
        else begin
            if (~div.start & (shift_count[15] | terminate_early) & ~div.done & ~terminate)
                div.done <= 1;
            else if (div.done)
                div.done <= 0;
        end
    end

endmodule
