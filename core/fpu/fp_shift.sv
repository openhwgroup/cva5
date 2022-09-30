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
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_shift #(
    parameter DATA_WIDTH = FRAC_WIDTH+3+GRS_WIDTH-1:0,
    parameter SHIFT_AMT_WIDTH = EXPO_WIDTH
)( 
    input logic [DATA_WIDTH-1:0] i_data,
    input logic [SHIFT_AMT_WIDTH-1:0] i_shift_amt,
    output logic [DATA_WIDTH-1:0] o_data
);

endmodule

