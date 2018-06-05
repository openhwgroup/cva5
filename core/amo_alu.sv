/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

import taiga_config::*;
import taiga_types::*;

module amo_alu(
        input amo_alu_inputs_t amo_alu_inputs,
        output logic[31:0] result
        );


    always_comb begin
        case (amo_alu_inputs.op)// <--unique as not all codes are in use
            AMO_SWAP : result = amo_alu_inputs.rs2;
            AMO_ADD : result = amo_alu_inputs.rs1_load + amo_alu_inputs.rs2;
            AMO_XOR : result = amo_alu_inputs.rs1_load ^ amo_alu_inputs.rs2;
            AMO_AND : result = amo_alu_inputs.rs1_load & amo_alu_inputs.rs2;
            AMO_OR : result = amo_alu_inputs.rs1_load | amo_alu_inputs.rs2;
            AMO_MIN : result = {1'b1, 30'b0};
            AMO_MAX : result = {1'b0, {30{1'b1}}};
            AMO_MINU : result = '0;
            AMO_MAXU : result = '1;
        endcase
    end


endmodule
