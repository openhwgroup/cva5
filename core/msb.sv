/*
 * Copyright © 2017, 2018 Eric Matthews,  Lesley Shannon
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
    logic [7:0] sub_sub_msb;
    logic [3:0] quadrant;

    always_comb begin
        for (int i=0; i<4; i++) begin
            quadrant[i] = |msb_input[i*8+:8];
        end

        msb[4] = quadrant[3] | quadrant[2];
        msb[3] = quadrant[3] | (~quadrant[2] & quadrant[1]);

        for (int i=0; i<8; i++) begin
            casez (msb_input[1+i*4+:3])
                3'b1?? : sub_sub_msb[i] = 1;
                3'b01? : sub_sub_msb[i] = 0;
                3'b001 : sub_sub_msb[i] = 1;
                default : sub_sub_msb[i] = 0;
            endcase
        end

        for (int i=0; i<4; i++) begin
            sub_msb[i][2] =  |msb_input[4+i*8+:4];
            sub_msb[i][1] =  (|msb_input[6+i*8+:2]) | (~|msb_input[4+i*8+:2] & |msb_input[2+i*8+:2]);
            sub_msb[i][0] = sub_msb[i][2] ? sub_sub_msb[(i*2) + 1] : sub_sub_msb[i*2];
        end

        msb[2:0] = sub_msb[msb[4:3]];
    end

endmodule