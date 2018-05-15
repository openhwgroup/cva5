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
        input logic lshift,
        output logic[XLEN-1:0] shifted_result
        );

    logic[XLEN-1:0] lshifter_input;
    logic[XLEN-1:0] shifter_in;
    logic[XLEN-1:0] lshifted;
    logic[XLEN-1:0] shifted;
    logic[XLEN-1:0] shiftx16, shiftx4, shiftx1;
    logic[XLEN*2-1:0] shiftx16_padded, shiftx4_padded;

    //Flip left shift input
    always_comb begin
        for (int i =0; i < 32; i++) begin
            lshifter_input[i] = shifter_input[31-i];
        end
    end
    assign shifter_in = lshift ? lshifter_input : shifter_input;
    //Bit flipping shared shifter
    //left shift occurs in decode logic

    always_comb begin
        case ({shift_amount[4],lshift})
            0: shiftx16 = shifter_input;
            1: shiftx16 = lshifter_input;
            2: shiftx16 = {{16{arith}}, shifter_input[15:0]};
            3: shiftx16 =  {{16{arith}}, lshifter_input[15:0]};
        endcase
    end

    assign shiftx16_padded = {{32{arith}}, shiftx16};

    always_comb begin
        case (shift_amount[3:2])
            0:  shiftx4 <= shiftx16_padded[31:0];
            1:  foreach (shiftx4[i]) shiftx4[i] <= shiftx16_padded[i+4];
            2:  foreach (shiftx4[i]) shiftx4[i] <= shiftx16_padded[i+8];
            3:  foreach (shiftx4[i]) shiftx4[i] <= shiftx16_padded[i+12];
        endcase
    end

    assign shiftx4_padded = {{32{arith}}, shiftx4};

    always_comb begin
        case (shift_amount[1:0])
            0:  shiftx1 <= shiftx4_padded[31:0];
            1:  foreach (shiftx1[i]) shiftx1[i] <= shiftx4_padded[i+1];
            2:  foreach (shiftx1[i]) shiftx1[i] <= shiftx4_padded[i+2];
            3:  foreach (shiftx1[i]) shiftx1[i] <= shiftx4_padded[i+3];
        endcase
    end

    //Flip left shift output
    always_comb begin
        for (int i =0; i < 32; i++) begin
            lshifted[i] = shiftx1[31-i];
        end
    end

   assign shifted_result =  lshift ? lshifted : shiftx1;

    //assign shifted_result =  lshift ? signed'({arith,shifter_input} <<< shift_amount) : signed'({arith,shifter_input} >>> shift_amount);

endmodule


