/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
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


