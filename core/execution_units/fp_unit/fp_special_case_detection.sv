/*
 * Copyright © 2019-2023 Yuhui Gao, Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module fp_special_case_detection

    #(
        parameter FRAC_W = 52,
        parameter EXPO_W = 11,
        parameter SUBNORMAL = 1
    )(
        input logic[EXPO_W-1:0] expo,
        input logic[FRAC_W-1:0] frac,
        output logic is_inf,
        output logic is_SNaN,
        output logic is_QNaN,
        output logic is_zero,
        output logic hidden
    );

    logic expo_all_1s;
    logic frac_lower_0s;
    assign expo_all_1s = &expo;
    assign frac_lower_0s = ~|frac[FRAC_W-2:0];

    assign hidden = |expo;
    assign is_inf = expo_all_1s & ~frac[FRAC_W-1] & frac_lower_0s; //Fully 0
    assign is_SNaN = expo_all_1s & ~frac[FRAC_W-1] & ~frac_lower_0s; //Leading 0 but not fully 0
    assign is_QNaN = expo_all_1s & frac[FRAC_W-1]; //Leading 1
    assign is_zero = SUBNORMAL ? ~hidden & ~frac[FRAC_W-1] & frac_lower_0s : ~hidden; //Flush to 0 when not enabled

endmodule
