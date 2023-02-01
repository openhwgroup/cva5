/*
 * Copyright © 2019-2023 Yuhui Gao, Lesley Shannon
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
 *             Yuhui Gao <yuhuig@sfu.ca>
 */

module fp_special_case_detection_mp
#(
    parameter FRAC_W=52,
    parameter EXPO_W=11
)(
    input logic [FRAC_W+EXPO_W:0] input1,
    output logic is_inf,
    output logic is_SNaN,
    output logic is_QNaN,
    output logic is_zero
);

    localparam FPLEN = 1 + FRAC_W + EXPO_W;

    logic expo_all_1s = &input1[FPLEN-2-:EXPO_W];

    assign is_inf = expo_all_1s & ~(|input1[0+:FRAC_W]);
    assign is_SNaN = expo_all_1s & ~input1[FRAC_W-1] & input1[FRAC_W-2] & ~|input1[FRAC_W-3:0];
    assign is_QNaN = expo_all_1s & input1[FRAC_W-1] & ~|input1[FRAC_W-2:0];
    assign is_zero = ~|input1[FPLEN-2-:EXPO_W]; // subnormal considered zero

endmodule

module fp_special_case_detection
    import taiga_config::*;

#(
    parameter FRAC_W=52,
    parameter EXPO_W=11
)(
    input logic [FRAC_W+EXPO_W:0] data_in,
    output logic is_inf,
    output logic is_SNaN,
    output logic is_QNaN,
    output logic is_zero,
    output logic hidden
);

    //unpack
    logic [EXPO_W-1:0] expo;
    assign expo = data_in[FRAC_W+EXPO_W-1 : FRAC_W];
    logic [FRAC_W-1:0] frac;
    assign frac = data_in[FRAC_W-1:0];

    //process
    assign hidden = |expo;

    logic expo_all_1s;
    assign expo_all_1s = &expo;
    logic frac_lower_0s;
    assign frac_lower_0s = ~|frac[FRAC_W-2:0];

    assign is_inf = expo_all_1s & ~frac[FRAC_W-1] & frac_lower_0s; //Fully 0
    assign is_SNaN = expo_all_1s & ~frac[FRAC_W-1] & ~frac_lower_0s; //Leading 0 but not fully 0
    assign is_QNaN = expo_all_1s & frac[FRAC_W-1]; //Leading 1
    generate if (ENABLE_SUBNORMAL)
        assign is_zero = ~hidden & ~frac[FRAC_W-1] & frac_lower_0s;
    else
        //flush to zero
        assign is_zero = ~hidden;
    endgenerate

endmodule
