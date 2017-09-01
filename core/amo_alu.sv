/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
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
        unique case (amo_alu_inputs.op)// <--unique as not all codes are in use
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
