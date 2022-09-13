/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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
 *                  Yuhui Gao <yuhuig@sfu.ca>
 */
import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;
import fpu_types::*;

module pre_normalize_general(
    input logic [FLEN-1:0] i_rs1,
    input logic i_hiddent,
    output logic [EXPO_WIDTH-1:0] left_shift_amt,
    output logic [FRAC_WIDTH:0] frac_normalized
);

    ////////////////////////////////////////////////////
    //Implementation
    //Unpack
    assign expo = rs2[FLEN-2-:EXPO_WIDTH];
    assign frac = {rs2_hidden_bit, rs2[FRAC_WIDTH-1:0]};
    
    //CLZ on subnormal input, and left shift to normalize
    //Assuming clz instances are optimized away when ENABLE_SUBNORMAL == 0
    generate if (FRAC_WIDTH+1 <= 32) begin
        clz frac_clz (
          .clz_input (32'(frac)),
          .clz (clz_with_prepended_0s[4:0])
        );
        assign left_shift_amt = clz_with_prepended_0s - (32 - (FRAC_WIDTH + 1));
    end else begin
        clz_tree frac_clz (
          .clz_input (64'(frac)),
          .clz (clz_with_prepended_0s[5:0])
        );
        assign left_shift_amt = clz_with_prepended_0s - (64 - (FRAC_WIDTH + 1));
    end endgenerate
    
    generate if (ENABLE_SUBNORMAL) 
      assign frac_normalized = frac << left_shift_amt;
    else
      assign frac_normalized = frac;
    endgenerate

endmodule

