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


module div_radix2_ET_full 
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
           //if (shift_count[31])
           else if (shift_count[31] | terminate_early)
               terminate <= 1;
       end
   end
 
   always_ff @ (posedge clk) begin
       if (rst)
           complete <= 0;
       else begin
            // if (shift_count[31])
           if (~start & (shift_count[31] | terminate_early) & ~complete & ~terminate)
               complete <= 1;
           else if (ack)
               complete <= 0;
       end
   end
 
endmodule