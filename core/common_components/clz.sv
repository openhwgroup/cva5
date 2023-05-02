/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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

module clz
        (
        input logic [31:0] clz_input,
        output logic [4:0] clz
        );

    logic [1:0] low_order_clz [7:0];
    logic [7:0] sub_clz;

    logic [1:0] upper_lower [3:0];
    //////////////////////////////////////////
    /* CLZ in groups of 4-bits (optimized for 6-input LUTs)
     *  Upper 3 bits of CLZ calculated directly from the subgroups
     *  Lower order bits [1:0] determined for each subgroup
     *  Lower order bits muxed with neighbor before final 4-1 mux using highest order bits [4:3]
     */
    //////////////////////////////////////////

    //31-28 index: 0, 3-0 index: 7
    const logic [1:0] clz_low_table [8] = '{2'd3, 2'd2, 2'd1, 2'd1, 2'd0, 2'd0, 2'd0, 2'd0};
    always_comb begin
        for (int i=0; i<8; i++) begin
            sub_clz[7-i] = ~|clz_input[(i*4) +: 4];
            low_order_clz[7-i] = clz_low_table[clz_input[(i*4) + 1 +: 3]];
        end

        clz[4] = &sub_clz[3:0]; //upper 16 all zero
        clz[3] = clz[4] ? &sub_clz[5:4] : &sub_clz[1:0];//upper 24 zero, or first 8 zero
        clz[2] =
            (sub_clz[0] & ~sub_clz[1]) |
            (&sub_clz[2:0] & ~sub_clz[3]) |
            (&sub_clz[4:0] & ~sub_clz[5]) |
            (&sub_clz[6:0]);

        for (int i=0; i<8; i+=2) begin
            upper_lower[i/2] = low_order_clz[{i[2:1],  sub_clz[i]}];
        end

        clz[1:0] = upper_lower[clz[4:3]];
    end

endmodule
