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
        output logic[XLEN-1:0] shifted_resultr,
        output logic[XLEN-1:0] shifted_resultl
        );

    logic[XLEN-1:0] shiftx8, shiftx2, shiftx1;
    logic[XLEN-1:0] preshifted_input;
    //Bit flipping shared shifter
    always_comb begin
        foreach (shifter_input[i])
            preshifted_input[i] = shifter_input[31-i];
    end

    always_comb begin//2
        case ({lshift, shift_amount[0]})
            0: shiftx1 = shifter_input[31:0];
            1: shiftx1 = {{1{arith}},shifter_input[31:1]};
            2: shiftx1 = preshifted_input[31:0];
            3: shiftx1 = {{1{arith}},preshifted_input[31:1]};
        endcase
    end

        always_comb begin//2
        case (shift_amount[2:1])
            0: shiftx2 = shiftx1[31:0];
            1: shiftx2 = {{2{arith}},shiftx1[31:2]};
            2: shiftx2 = {{4{arith}},shiftx1[31:4]};
            3: shiftx2 = {{6{arith}},shiftx1[31:6]};
        endcase
    end

    always_comb begin//8
        case (shift_amount[4:3])
            0: shiftx8 = shiftx2[31:0];
            1: shiftx8 = {{8{arith}},shiftx2[31:8]};
            2: shiftx8 = {{16{arith}},shiftx2[31:16]};
            3: shiftx8 = {{24{arith}},shiftx2[31:24]};
        endcase
    end
    assign shifted_resultr = shiftx8;

    always_comb begin
        foreach (shifter_input[i])
            shifted_resultl[i] = shiftx8[31-i];
    end

endmodule


