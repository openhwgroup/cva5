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


module div_radix16
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
   logic [C_WIDTH-1:0] shift_count;

   logic [C_WIDTH+3:0] PR;
   logic [C_WIDTH+3:0] PR_lower;
   logic [C_WIDTH+3:0] PR_upper;
   logic [C_WIDTH-1:0] Q_lower;
   logic [C_WIDTH-1:0] Q_upper;   
   
   logic [6:0] new_PR_sign;
   logic [C_WIDTH+4:0] new_PR_8;
   logic [C_WIDTH+4:0] new_PR [6:0];

   logic [C_WIDTH+3:0] B_6;
   logic [C_WIDTH+3:0] B_10;
   logic [C_WIDTH+3:0] B_12;
   logic [C_WIDTH+3:0] B_14;        

   //implementation
   ////////////////////////////////////////////////////
   assign new_PR_8  = {1'b0, PR} - {1'b0, {1'b0, B, 3'b000}};
   assign new_PR[0]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {4'b0000, B}}                      : {1'b0, PR} - {1'b0, {1'b0, B, 3'b000}} - {4'b0000, B};
   assign new_PR[1]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {3'b000, B, 1'b0}}                 : {1'b0, PR} - {1'b0, B_10};
   assign new_PR[2]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {3'b000, B, 1'b0}} - {4'b0000, B}  : {1'b0, PR} - {1'b0, B_10} - {4'b0000, B};
   assign new_PR[3]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {2'b00, B, 2'b00}}                 : {1'b0, PR} - {1'b0, B_12};
   assign new_PR[4]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {2'b00, B, 2'b00}} - {4'b0000, B}  : {1'b0, PR} - {1'b0, B_12} - {4'b0000, B};
   assign new_PR[5]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, B_6}                               : {1'b0, PR} - {1'b0, B_14};
   assign new_PR[6]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, B_6} - {4'b0000, B}                : {1'b0, PR} - {1'b0, B_14} - {4'b0000, B};

   assign new_PR_sign = {new_PR[6][C_WIDTH+4], new_PR[5][C_WIDTH+4], new_PR[4][C_WIDTH+4],
                         new_PR[3][C_WIDTH+4], new_PR[2][C_WIDTH+4], new_PR[1][C_WIDTH+4],
                         new_PR[0][C_WIDTH+4]};

   //Shift reg for
   always_ff @ (posedge clk) begin
       shift_count[0] <= start;
       shift_count[31:1] <= shift_count[30:0];
   end
   
   always_comb begin
        PR_lower = ({PR[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(new_PR_sign[0])}});
        Q_lower = ({Q[C_WIDTH-5:0], 4'b0000} & {C_WIDTH{(new_PR_sign[0])}});
        for (int i = 1; i < 7; i = i+1) begin
            PR_lower = PR_lower | ({new_PR[i-1][C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(~new_PR_sign[i-1] & new_PR_sign[i])}});
            Q_lower  = Q_lower  | ({Q[C_WIDTH-5:0], i[3:0]} & {C_WIDTH{(~new_PR_sign[i-1] & new_PR_sign[i])}});
        end
        PR_lower = PR_lower | ({new_PR[6][C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(~new_PR_sign[6])}});
        Q_lower  = Q_lower  | ({Q[C_WIDTH-5:0], 4'b0111} & {C_WIDTH{(~new_PR_sign[6])}});
        
        PR_upper = {new_PR_8[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){new_PR_sign[0]}};
        Q_upper  = {Q[C_WIDTH-5:0], 4'b1000} & {C_WIDTH{new_PR_sign[0]}};
        for (int i = 1; i < 7; i = i+1) begin
            PR_upper = PR_upper | ({new_PR[i-1][C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(~new_PR_sign[i-1] & new_PR_sign[i])}});
            Q_upper  = Q_upper  | ({Q[C_WIDTH-5:0], (i[3:0] | 4'b1000)} & {C_WIDTH{(~new_PR_sign[i-1] & new_PR_sign[i])}});
        end
        PR_upper = PR_upper | ({new_PR[6][C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(~new_PR_sign[6])}});
        Q_upper  = Q_upper  | ({Q[C_WIDTH-5:0], 4'b1111} & {C_WIDTH{(~new_PR_sign[6])}});
   end 

   always_ff @ (posedge clk) begin
       if (start) begin
           B_6  <= {2'b00, B, 2'b00} + {3'b000, B, 1'b0};
           B_10 <= {1'b0, B, 3'b000} + {3'b000, B, 1'b0};
           B_12 <= {1'b0, B, 3'b000} + {2'b00, B, 2'b00};
           B_14 <= {1'b0, B, 3'b000} + {2'b00, B, 2'b00} + {3'b000, B, 1'b0};

           PR <= {{(C_WIDTH){1'b0}}, A[C_WIDTH-1:C_WIDTH-4]};
           Q <= {A[C_WIDTH-5:0], 4'b0000};
       end
       else if (~terminate) begin
          casez (new_PR_8[C_WIDTH+4])
              1'b1 : begin
                  PR <= PR_lower;
                  Q <= Q_lower;
              end
              1'b0 : begin
                  PR <= PR_upper;
                  Q <= Q_upper;
              end
              default : begin
                  PR <= 'x;
                  Q <= 'x;
              end
          endcase
       end
   end

   assign R = PR[C_WIDTH+3:4];

   always_ff @ (posedge clk) begin
       if (rst)
           terminate <= 0;
       else begin
           if (start)
               terminate <= 0;
           if (shift_count[7])
               terminate <= 1;
       end
   end

   always_ff @ (posedge clk) begin
       if (rst)
           complete <= 0;
       else begin
           if (shift_count[7])
               complete <= 1;
           else if (ack)
               complete <= 0;
       end
   end

endmodule
