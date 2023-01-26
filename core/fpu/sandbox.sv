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

module sandbox
    import taiga_config::*;
#(
    parameter SANDBOX_FRAC_W=52,
    parameter SANDBOX_EXPO_W=11
)(
    input logic [FLEN-1:0] data_in,
    output logic [FLEN-1:0] data_out
);

    logic sign_in;
    logic [EXPO_WIDTH-1:0] expo_in;
    logic [FRAC_WIDTH-1:0] frac_in;
    logic sign_sandboxed;
    logic [SANDBOX_EXPO_W-1:0] expo_sandboxed;
    logic [SANDBOX_FRAC_W-1:0] frac_sandboxed;

    //unpack
    assign {sign_in, expo_in, frac_in} = data_in;

    //sandbox
    generate if (SANDBOX_EXPO_W < EXPO_WIDTH)
        assign expo_sandboxed = expo_in[SANDBOX_EXPO_W-1:0] | {SANDBOX_EXPO_W{(|expo_in[EXPO_WIDTH-1:SANDBOX_EXPO_W])}}; // detect overflow/NaN
    else
        assign expo_sandboxed = expo_in[SANDBOX_EXPO_W-1:0];
    endgenerate

    assign sign_sandboxed = sign_in;
    assign frac_sandboxed = frac_in[FRAC_WIDTH-1-:SANDBOX_FRAC_W];

    //output
    assign data_out = {sign_sandboxed, EXPO_WIDTH'(expo_sandboxed), {frac_sandboxed, {(FRAC_WIDTH-SANDBOX_FRAC_W){1'b0}}}};

endmodule
