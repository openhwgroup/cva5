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
    //Finds MSB for 4x 8-bit segments in parallel
    //Is smaller and faster than checking the full width sequentially (i.e. from 0 to 31)

    logic [1:0] sub_sub_msb [3:0];

    //    always_comb begin
    //        msb = 0;
    //        for (int i=1; i<31; i=i+1) begin
    //            if (msb_input[i]) msb = i;
    //        end
    //    end

    always_comb begin
        for (int i=0; i<4; i=i+1) begin

            //upper bit is set only if any of the upper 4-bits are set
            sub_msb[i][2] = |msb_input[4+i*8+:4];
            sub_msb[i][1] = (|msb_input[4+i*8+:4]) | (~(|msb_input[6+i*8+:2]) & (|msb_input[2+i*8+:2]));

            casez (msb_input[5+i*8+:3])
                3'b1?? : sub_sub_msb[i][0] = 1;
                3'b01? : sub_sub_msb[i][0] = 0;
                3'b001 : sub_sub_msb[i][0] = 1;
                default : sub_sub_msb[i][0] = 0;
            endcase

            casez (msb_input[1+i*8+:3])
                3'b1?? : sub_sub_msb[i][1] = 1;
                3'b01? : sub_sub_msb[i][1] = 0;
                3'b001 : sub_sub_msb[i][1] = 1;
                default : sub_sub_msb[i][1] = 0;
            endcase

            sub_msb[i][0] = sub_msb[i][2] ? sub_sub_msb[i][0] : sub_sub_msb[i][1];
        end

        msb[4] = (|msb_input[31:26]) | (|msb_input[25:20]) | (|msb_input[19:16]);//upper 16 bits
        msb[3] = (|msb_input[31:26]) | (|msb_input[25:24]) |
            ((~|msb_input[23:16]) & (|msb_input[15:8]));

        msb[2:0] = sub_msb[msb[4:3]];

    end

endmodule

