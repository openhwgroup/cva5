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
 
import taiga_config::*;
import taiga_types::*;

module barrel_shifter (
        input logic[XLEN-1:0] shifter_input,
        input logic[4:0] shift_amount,
        input logic arith,
        input logic left_shift,
        output logic[XLEN-1:0]shifted_result
        );

    logic[XLEN-1:0] lshifter_input;
    logic[XLEN-1:0] shifter_in;
    logic[XLEN-1:0] lshifted;
    logic[XLEN:0] shifted;


    //Bit flipping shared shifter
   // always_comb begin
      //  for (int i =0; i < 32; i++) begin
      //      lshifter_input[i] = shifter_input[31-i];
       // end
    //end

    //assign shifter_in = left_shift ? lshifter_input : shifter_input;
    assign shifted = signed'({arith,shifter_input}) >>> shift_amount;


    always_comb begin
        for (int i =0; i < 32; i++) begin
            lshifted[i] = shifted[31-i];
        end
    end
    //assign lshifted = {<<{shifted}};//if stream operator supported

    assign shifted_result = left_shift ? lshifted : shifted[31:0];


endmodule


