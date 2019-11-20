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


module div_radix2_ET_full 
        (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
        );
 
   logic terminate;
 
   logic [div.DATA_WIDTH:0] new_PR;
   logic [div.DATA_WIDTH:0] PR;
 
   logic [div.DATA_WIDTH-1:0] shift_count;
    
   logic negative_sub_rst;
   logic [div.DATA_WIDTH-1:0] AR_r;
   logic [div.DATA_WIDTH-1:0] Q_temp;
   logic [5:0] shift_num_R;
   logic [5:0] shift_num_Q;
   logic [div.DATA_WIDTH*2:0] combined;
   logic [div.DATA_WIDTH*2:0] combined_r;
   logic terminate_early;
   logic terminate_early_r;
    
   //implementation
   ////////////////////////////////////////////////////
   assign new_PR = PR - {1'b0, div.divisor};
   assign negative_sub_rst = new_PR[div.DATA_WIDTH];
 
   always_ff @ (posedge clk) begin
       if (div.start)
           shift_count <= 32'd1;
       else
           shift_count <= {shift_count[30:0], div.start};
   end
 
   always_ff @ (posedge clk) begin
       if (div.start) begin
          shift_num_R <= 1;
          shift_num_Q <= 32;
       end 
       else if (~terminate & ~terminate_early) begin
           shift_num_R <= shift_num_R + 1;
           shift_num_Q <= shift_num_Q - 1;
       end 
   end 
    
   assign combined = {PR, AR_r} >> shift_num_R;
    
   assign div.remainder = combined[div.DATA_WIDTH-1:0];
   assign terminate_early = div.divisor > div.remainder;
   assign div.quotient = terminate_early ? (Q_temp << shift_num_Q) : Q_temp;
 
   always_ff @ (posedge clk) begin
       if (div.start) begin
           PR <= {(div.DATA_WIDTH)'(1'b0), div.dividend[div.DATA_WIDTH-1]};
           Q_temp <= '0;
           AR_r <= {div.dividend[div.DATA_WIDTH-2:0], 1'b0};
       end
       else if (~terminate & ~terminate_early) begin
            PR <= negative_sub_rst ? {PR[div.DATA_WIDTH-1:0], AR_r[div.DATA_WIDTH-1]} :
              {new_PR[div.DATA_WIDTH-1:0], AR_r[div.DATA_WIDTH-1]};
            Q_temp <= {Q_temp[div.DATA_WIDTH-2:0], ~negative_sub_rst};
            AR_r <= {AR_r[div.DATA_WIDTH-2:0], 1'b0};
       end
   end
 
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
           //if (shift_count[31])
           else if (shift_count[31] | terminate_early)
               terminate <= 1;
       end
   end
 
   always_ff @ (posedge clk) begin
       if (rst)
           div.done <= 0;
       else begin
            // if (shift_count[31])
           if (~div.start & (shift_count[31] | terminate_early) & ~div.done & ~terminate)
               div.done <= 1;
           else if (div.done)
               div.done <= 0;
       end
   end
 
endmodule
