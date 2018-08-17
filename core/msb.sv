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
 
module msb
        (
        input logic [31:0] msb_input,
        output logic [4:0] msb
        );

    logic [2:0] sub_msb [3:0];
    logic index16thBit;
    logic index8thBit;

    always_comb begin
        msb[4] = |msb_input[31:16];
        msb[3] = (|msb_input[31:24]) | (|msb_input[15:8] & ~|msb_input[23:16]);

        casex (msb_input[31:25])
            7'b1xxxxxx: sub_msb[3] = 7;
            7'b01xxxxx: sub_msb[3] = 6;
            7'b001xxxx: sub_msb[3] = 5;
            7'b0001xxx: sub_msb[3] = 4;
            7'b00001xx: sub_msb[3] = 3;
            7'b000001x: sub_msb[3] = 2;
            7'b0000001: sub_msb[3] = 1;
            default: sub_msb[3] = 0;
        endcase

        casex (msb_input[23:17])
            7'b1xxxxxx: sub_msb[2] = 7;
            7'b01xxxxx: sub_msb[2] = 6;
            7'b001xxxx: sub_msb[2] = 5;
            7'b0001xxx: sub_msb[2] = 4;
            7'b00001xx: sub_msb[2] = 3;
            7'b000001x: sub_msb[2] = 2;
            7'b0000001: sub_msb[2] = 1;
            default: sub_msb[2] = 0;
        endcase

        casex (msb_input[15: 9])
            7'b1xxxxxx: sub_msb[1] = 7;
            7'b01xxxxx: sub_msb[1] = 6;
            7'b001xxxx: sub_msb[1] = 5;
            7'b0001xxx: sub_msb[1] = 4;
            7'b00001xx: sub_msb[1] = 3;
            7'b000001x: sub_msb[1] = 2;
            7'b0000001: sub_msb[1] = 1;
            default: sub_msb[1] = 0;
        endcase
        
        casex (msb_input[ 7: 1])
            7'b1xxxxxx: sub_msb[0] = 7;
            7'b01xxxxx: sub_msb[0] = 6;
            7'b001xxxx: sub_msb[0] = 5;
            7'b0001xxx: sub_msb[0] = 4;
            7'b00001xx: sub_msb[0] = 3;
            7'b000001x: sub_msb[0] = 2;
            7'b0000001: sub_msb[0] = 1;
            default: sub_msb[0] = 0;
        endcase

        case (msb[4:3])
            0: msb[2:0] = sub_msb[0];
            1: msb[2:0] = sub_msb[1];
            2: msb[2:0] = sub_msb[2];
            3: msb[2:0] = sub_msb[3];
        endcase
    end 
    
endmodule