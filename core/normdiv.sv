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

 module normdiv //radix-2
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
 
    logic terminate;
 
    logic [C_WIDTH:0] new_PR;
    logic [C_WIDTH:0] PR;
 
    logic [C_WIDTH-1:0] shift_count;
    
    logic negative_sub_rst;
    logic [C_WIDTH-1:0] B_r;
    logic [C_WIDTH-1:0] AR_r;
    logic [C_WIDTH-1:0] Q_temp;
    logic [5:0] shift_num_R;
    logic [5:0] shift_num_Q;
    logic [C_WIDTH*2:0] combined;
    logic [C_WIDTH*2:0] combined_r;
    logic terminate_early;
    logic terminate_early_r;
    
    //implementation
    ////////////////////////////////////////////////////
    assign new_PR = PR - {1'b0, B_r};
    assign negative_sub_rst = new_PR[C_WIDTH];
 
    always_ff @ (posedge clk) begin
        if (start)
            shift_count <= 32'd1;
        else
            shift_count <= {shift_count[30:0], start}; 
    end
 
    always_ff @ (posedge clk) begin
        if (start) begin
           shift_num_R <= 1;
           shift_num_Q <= 32;
        end 
        else if (~terminate & ~terminate_early) begin
            shift_num_R <= shift_num_R + 1;
            shift_num_Q <= shift_num_Q - 1;
        end 
    end 
    
    assign combined = {PR, AR_r} >> shift_num_R;
    
    assign R = combined[C_WIDTH-1:0];
    assign terminate_early = B_r > R;
    assign Q = terminate_early ? (Q_temp << shift_num_Q) : Q_temp;
 
    always_ff @ (posedge clk) begin
        if (start) begin
            PR <= {{(C_WIDTH-2){1'b0}}, A[C_WIDTH-1]};
            Q_temp <= '0;
            AR_r <= {A[C_WIDTH-2:0], 1'b0};
            B_r <= B;
        end
        else if (~terminate & ~terminate_early) begin
             PR <= negative_sub_rst ? {PR[C_WIDTH-1:0], AR_r[C_WIDTH-1]} : 
               {new_PR[C_WIDTH-1:0], AR_r[C_WIDTH-1]};               
             Q_temp <= {Q_temp[C_WIDTH-2:0], ~negative_sub_rst};
             AR_r <= {AR_r[C_WIDTH-2:0], 1'b0};
        end
    end
 
    always_ff @ (posedge clk) begin
        if (rst)
            terminate <= 0;
        else begin
            if (start)
                terminate <= 0;
            else if (shift_count[31] | terminate_early)
                terminate <= 1;
        end
    end
 
    always_ff @ (posedge clk) begin
        if (rst)
            complete <= 0;
        else begin
            if (~start & (shift_count[31] | terminate_early) & ~complete & ~terminate)
                complete <= 1;
            else if (ack)
                complete <= 0;
        end
    end
 
 endmodule

// module normdiv //radix-2
//        #(
//        parameter C_WIDTH = 32
//        )
//        (
//        input logic clk,
//        input logic rst,
//        input logic start,
//        input logic ack,
//        input logic [C_WIDTH-1:0] A,
//        input logic [C_WIDTH-1:0] B,
//        output logic [C_WIDTH-1:0] Q,
//        output logic [C_WIDTH-1:0] R,
//        output logic complete
//        );

//    logic terminate;

//    logic [C_WIDTH-1:0] B_r;
//    logic [C_WIDTH:0] new_PR;
//    logic [C_WIDTH:0] PR;

//    logic [C_WIDTH-1:0] shift_count;

//    //implementation
//    ////////////////////////////////////////////////////
//    assign  new_PR = PR - B_r;
//    logic negative_sub_rst = new_PR[C_WIDTH];

//    always_ff @ (posedge clk) begin
//        shift_count <= {shift_count[30:0], start};
//    end

//    always_ff @ (posedge clk) begin
//        if (start) begin
//            PR <= {{(C_WIDTH-2){1'b0}}, A[C_WIDTH-1]};
//            Q <= {A[C_WIDTH-2:0], 1'b0};
//            B_r <= B;
//        end
//        else if (~terminate) begin
//            case (negative_sub_rst)
//                1'b1 : begin
//                    PR <= {PR[C_WIDTH-1:0], Q[C_WIDTH-1]};
//                    Q <= {Q[C_WIDTH-2:0], 1'b0};                    
//                end 
//                1'b0 : begin
//                    PR <= {new_PR[C_WIDTH-1:0], Q[C_WIDTH-1]};
//                    Q <= {Q[C_WIDTH-2:0], 1'b1};                    
//                end
//            endcase
//        end
//    end

//    assign R = PR[C_WIDTH:1];

//    always_ff @ (posedge clk) begin
//        if (rst)
//            terminate <= 0;
//        else begin
//            if (start)
//                terminate <= 0;
//            if (shift_count[31])
//                terminate <= 1;
//        end
//    end

//    always_ff @ (posedge clk) begin
//        if (rst)
//            complete <= 0;
//        else begin
//            if (shift_count[31])
//                complete <= 1;
//            else if (ack)
//                complete <= 0;
//        end
//    end

// endmodule

// module normdiv //radix-4
//         #(
//         parameter C_WIDTH = 32
//         )
//         (
//         input logic clk,
//         input logic rst,
//         input logic start,
//         input logic ack,
//         input logic [C_WIDTH-1:0] A,
//         input logic [C_WIDTH-1:0] B,
//         output logic [C_WIDTH-1:0] Q,
//         output logic [C_WIDTH-1:0] R,
//         output logic complete
//         );

//     logic terminate;
//     logic [C_WIDTH/2-1:0] shift_count;

//     logic [C_WIDTH+1:0] PR;
//     logic [2:0] new_PR_sign;
//     logic [C_WIDTH+2:0] new_PR_1;
//     logic [C_WIDTH+2:0] new_PR_2;
//     logic [C_WIDTH+2:0] new_PR_3;
//     logic [C_WIDTH+1:0] B_1;
//     logic [C_WIDTH+1:0] B_2;
//     logic [C_WIDTH+1:0] B_3;

//     //implementation
//     ////////////////////////////////////////////////////
//     assign new_PR_1 = {1'b0, PR} - {1'b0, B_1};
//     assign new_PR_2 = {1'b0, PR} - {1'b0, B_2};
//     assign new_PR_3 = {1'b0, PR} - {1'b0, B_3};
//     assign new_PR_sign = {new_PR_3[C_WIDTH+2], new_PR_2[C_WIDTH+2], new_PR_1[C_WIDTH+2]};

//     //Shift reg for
//     always_ff @ (posedge clk) begin
//         shift_count[0] <= start;
//         shift_count[15:1] <= shift_count[14:0];
//     end

//     always_ff @ (posedge clk) begin
//         if (start) begin
//             B_1 <= {2'b0, B};           //1xB
//             B_2 <= {1'b0, B, 1'b0};     //2xB
//             B_3 <= {1'b0, B, 1'b0} + B; //3xB

//             PR <= {{(C_WIDTH-1){1'b0}}, A[C_WIDTH-1:C_WIDTH-2]};
//             Q <= {A[C_WIDTH-3:0], 2'b00};
//         end
//         else if (~terminate) begin
//             casex (new_PR_sign)
//                 3'b111 : begin
//                     PR <= {PR[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-2]};
//                     Q <= {Q[C_WIDTH-3:0], 2'b00};
//                 end
//                 3'b110 : begin
//                     PR <= {new_PR_1[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-2]};
//                     Q <= {Q[C_WIDTH-3:0], 2'b01};
//                 end
//                 3'b100 : begin
//                     PR <= {new_PR_2[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-2]};
//                     Q <= {Q[C_WIDTH-3:0], 2'b10};
//                 end
//                 3'b000 : begin
//                     PR <= {new_PR_3[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-2]};
//                     Q <= {Q[C_WIDTH-3:0], 2'b11};
//                 end
//                 default begin
//                     PR <= 'x;
//                     Q <= 'x;
//                 end 
//             endcase
//         end
//     end

//     assign R = PR[C_WIDTH+1:2];

//     always_ff @ (posedge clk) begin
//         if (rst)
//             terminate <= 0;
//         else begin
//             if (start)
//                 terminate <= 0;
//             if (shift_count[15])
//                 terminate <= 1;
//         end
//     end

//     always_ff @ (posedge clk) begin
//         if (rst)
//             complete <= 0;
//         else begin
//             if (shift_count[15])
//                 complete <= 1;
//             else if (ack)
//                 complete <= 0;
//         end
//     end

// endmodule

//module normdiv //radix-16
//       #(
//       parameter C_WIDTH = 32
//       )
//       (
//       input logic clk,
//       input logic rst,
//       input logic start,
//       input logic ack,
//       input logic [C_WIDTH-1:0] A,
//       input logic [C_WIDTH-1:0] B,
//       output logic [C_WIDTH-1:0] Q,
//       output logic [C_WIDTH-1:0] R,
//       output logic complete
//       );

//   logic terminate;
//   logic [C_WIDTH-1:0] shift_count;

//   logic [C_WIDTH+3:0] PR;
//   logic [C_WIDTH+3:0] PR_lower;
//   logic [C_WIDTH+3:0] PR_upper;
//   logic [C_WIDTH-1:0] Q_lower;
//   logic [C_WIDTH-1:0] Q_upper;   
   
//   logic [6:0] new_PR_sign;
//   logic [C_WIDTH+4:0] new_PR_8;
//   logic [C_WIDTH+4:0] new_PR [6:0];

//   logic [C_WIDTH+3:0] B_6;
//   logic [C_WIDTH+3:0] B_10;
//   logic [C_WIDTH+3:0] B_12;
//   logic [C_WIDTH+3:0] B_14;        

//   //implementation
//   ////////////////////////////////////////////////////
//   assign new_PR_8  = {1'b0, PR} - {1'b0, {1'b0, B, 3'b000}};
//   assign new_PR[0]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {4'b0000, B}}                      : {1'b0, PR} - {1'b0, {1'b0, B, 3'b000}} - {4'b0000, B};
//   assign new_PR[1]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {3'b000, B, 1'b0}}                 : {1'b0, PR} - {1'b0, B_10};
//   assign new_PR[2]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {3'b000, B, 1'b0}} - {4'b0000, B}  : {1'b0, PR} - {1'b0, B_10} - {4'b0000, B};
//   assign new_PR[3]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {2'b00, B, 2'b00}}                 : {1'b0, PR} - {1'b0, B_12};
//   assign new_PR[4]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, {2'b00, B, 2'b00}} - {4'b0000, B}  : {1'b0, PR} - {1'b0, B_12} - {4'b0000, B};
//   assign new_PR[5]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, B_6}                               : {1'b0, PR} - {1'b0, B_14};
//   assign new_PR[6]  = new_PR_8[C_WIDTH+4] ? {1'b0, PR} - {1'b0, B_6} - {4'b0000, B}                : {1'b0, PR} - {1'b0, B_14} - {4'b0000, B};

//   assign new_PR_sign = {new_PR[6][C_WIDTH+4], new_PR[5][C_WIDTH+4], new_PR[4][C_WIDTH+4],
//                         new_PR[3][C_WIDTH+4], new_PR[2][C_WIDTH+4], new_PR[1][C_WIDTH+4],
//                         new_PR[0][C_WIDTH+4]};

//   //Shift reg for
//   always_ff @ (posedge clk) begin
//       shift_count[0] <= start;
//       shift_count[31:1] <= shift_count[30:0];
//   end
   
//   always_comb begin
//        PR_lower = ({PR[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(new_PR_sign[0])}});
//        Q_lower = ({Q[C_WIDTH-5:0], 4'b0000} & {C_WIDTH{(new_PR_sign[0])}});
//        for (int i = 1; i < 7; i = i+1) begin
//            PR_lower = PR_lower | ({new_PR[i-1][C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(~new_PR_sign[i-1] & new_PR_sign[i])}});
//            Q_lower  = Q_lower  | ({Q[C_WIDTH-5:0], i[3:0]} & {C_WIDTH{(~new_PR_sign[i-1] & new_PR_sign[i])}});
//        end
//        PR_lower = PR_lower | ({new_PR[6][C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(~new_PR_sign[6])}});
//        Q_lower  = Q_lower  | ({Q[C_WIDTH-5:0], 4'b0111} & {C_WIDTH{(~new_PR_sign[6])}});
        
//        PR_upper = {new_PR_8[C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){new_PR_sign[0]}};
//        Q_upper  = {Q[C_WIDTH-5:0], 4'b1000} & {C_WIDTH{new_PR_sign[0]}};
//        for (int i = 1; i < 7; i = i+1) begin
//            PR_upper = PR_upper | ({new_PR[i-1][C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(~new_PR_sign[i-1] & new_PR_sign[i])}});
//            Q_upper  = Q_upper  | ({Q[C_WIDTH-5:0], (i[3:0] | 4'b1000)} & {C_WIDTH{(~new_PR_sign[i-1] & new_PR_sign[i])}});
//        end
//        PR_upper = PR_upper | ({new_PR[6][C_WIDTH-1:0], Q[C_WIDTH-1:C_WIDTH-4]} & {(C_WIDTH+4){(~new_PR_sign[6])}});
//        Q_upper  = Q_upper  | ({Q[C_WIDTH-5:0], 4'b1111} & {C_WIDTH{(~new_PR_sign[6])}});
//   end 

//   always_ff @ (posedge clk) begin
//       if (start) begin
//           B_6  <= {2'b00, B, 2'b00} + {3'b000, B, 1'b0};
//           B_10 <= {1'b0, B, 3'b000} + {3'b000, B, 1'b0};
//           B_12 <= {1'b0, B, 3'b000} + {2'b00, B, 2'b00};
//           B_14 <= {1'b0, B, 3'b000} + {2'b00, B, 2'b00} + {3'b000, B, 1'b0};

//           PR <= {{(C_WIDTH){1'b0}}, A[C_WIDTH-1:C_WIDTH-4]};
//           Q <= {A[C_WIDTH-5:0], 4'b0000};
//       end
//       else if (~terminate) begin
//          casez (new_PR_8[C_WIDTH+4])
//              1'b1 : begin
//                  PR <= PR_lower;
//                  Q <= Q_lower;
//              end
//              1'b0 : begin
//                  PR <= PR_upper;
//                  Q <= Q_upper;
//              end
//              default : begin
//                  PR <= 'x;
//                  Q <= 'x;
//              end
//          endcase
//       end
//   end

//   assign R = PR[C_WIDTH+3:4];

//   always_ff @ (posedge clk) begin
//       if (rst)
//           terminate <= 0;
//       else begin
//           if (start)
//               terminate <= 0;
//           if (shift_count[7])
//               terminate <= 1;
//       end
//   end

//   always_ff @ (posedge clk) begin
//       if (rst)
//           complete <= 0;
//       else begin
//           if (shift_count[7])
//               complete <= 1;
//           else if (ack)
//               complete <= 0;
//       end
//   end

//endmodule