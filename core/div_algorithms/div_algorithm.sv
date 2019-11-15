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
 *             Alec Lu <alec_lu@sfu.ca>
 */

import taiga_config::*;
import taiga_types::*;

module div_algorithm
        #(
        parameter C_WIDTH = 32
        )
        (
        input logic clk,
        input logic rst,
        input logic start,
        input logic ack,
        input logic [C_WIDTH-1:0] A,
        input logic [C_WIDTH-1:0] B,
        output logic [C_WIDTH-1:0] Q,
        output logic [C_WIDTH-1:0] R,
        output logic complete,
        output logic B_is_zero
        );

    generate
        case(DIV_ALGORITHM)
            RADIX_2 : div_radix2 #(XLEN) div (.*);
            RADIX_2_EARLY_TERMINATE : div_radix2_ET #(XLEN) div (.*);
            RADIX_2_EARLY_TERMINATE_FULL : div_radix2_ET_full #(XLEN) div (.*);
            RADIX_4 : div_radix4 #(XLEN) div (.*);
            RADIX_4_EARLY_TERMINATE : div_radix4_ET #(XLEN) div (.*);
            RADIX_4_EARLY_TERMINATE_FULL: div_radix4_ET_full #(XLEN) div (.*);
            RADIX_8 : div_radix8 #(XLEN) div (.*);
            RADIX_8_EARLY_TERMINATE : div_radix8_ET #(XLEN) div (.*);
            RADIX_16 : div_radix16 #(XLEN) div (.*);
            QUICK_NAIVE : div_quick_naive #(XLEN) div (.*);
            QUICK_CLZ : div_quick_clz #(XLEN) div (.*);
            QUICK_CLZ_MK2 : div_quick_clz_mk2 #(XLEN) div (.*);
            QUICK_RADIX_4 : div_quick_radix_4 #(XLEN) div (.*);
            default : $error("invalid div selection");
        endcase
    endgenerate

endmodule




