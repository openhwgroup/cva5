/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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
             RADIX_2 : div_radix2 #(.DIV_WIDTH(32)) div_block (.clk(clk), .rst(rst), .div(div));
             QUICK_CLZ : div_quick_clz #(.DIV_WIDTH(32)) div_block (.clk(clk), .rst(rst), .div(div));
        endcase
    endgenerate

endmodule




