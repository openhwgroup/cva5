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
        (
        input logic clk,
        input logic rst,
        unsigned_division_interface.divider div
        );

    generate
        case(DIV_ALGORITHM)
             RADIX_2 : div_radix2 div_block (.*);
             RADIX_2_EARLY_TERMINATE : div_radix2_ET div_block (.*);
             RADIX_2_EARLY_TERMINATE_FULL : div_radix2_ET_full div_block (.*);
             RADIX_4 : div_radix4 div_block (.*);
             RADIX_4_EARLY_TERMINATE : div_radix4_ET div_block (.*);
             RADIX_4_EARLY_TERMINATE_FULL: div_radix4_ET_full div_block (.*);
             RADIX_8 : div_radix8 div_block (.*);
             RADIX_8_EARLY_TERMINATE : div_radix8_ET div_block (.*);
             RADIX_16 : div_radix16 div_block (.*);
             QUICK_NAIVE : div_quick_naive div_block (.*);
             QUICK_CLZ : div_quick_clz div_block (.*);
             QUICK_CLZ_MK2 : div_quick_clz_mk2 div_block (.*);
             QUICK_RADIX_4 : div_quick_radix_4 div_block (.*);
            default : $error("invalid div selection");
        endcase
    endgenerate

endmodule




