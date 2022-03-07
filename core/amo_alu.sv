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

module amo_alu

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    (
        input amo_alu_inputs_t amo_alu_inputs,
        output logic[31:0] result
    );

    logic rs1_smaller_than_rs2;
     logic signed [32:0] rs1_ext;
     logic signed [32:0] rs2_ext;

     //bit 4 for unsigned
    assign rs1_ext = {(~amo_alu_inputs.op[4] & amo_alu_inputs.rs1_load[31]), amo_alu_inputs.rs1_load};
    assign rs2_ext = {(~amo_alu_inputs.op[4] & amo_alu_inputs.rs2[31]), amo_alu_inputs.rs2};

    assign rs1_smaller_than_rs2 = rs1_ext < rs2_ext;

    /* verilator lint_off CASEINCOMPLETE */
    always_comb begin
        case (amo_alu_inputs.op)// <--unique as not all codes are in use
            AMO_SWAP_FN5 : result = amo_alu_inputs.rs2;
            AMO_ADD_FN5 : result = amo_alu_inputs.rs1_load + amo_alu_inputs.rs2;
            AMO_XOR_FN5 : result = amo_alu_inputs.rs1_load ^ amo_alu_inputs.rs2;
            AMO_AND_FN5 : result = amo_alu_inputs.rs1_load & amo_alu_inputs.rs2;
            AMO_OR_FN5 : result = amo_alu_inputs.rs1_load | amo_alu_inputs.rs2;
            AMO_MIN_FN5 : result = rs1_smaller_than_rs2 ? amo_alu_inputs.rs1_load : amo_alu_inputs.rs2;
            AMO_MAX_FN5 : result = rs1_smaller_than_rs2 ? amo_alu_inputs.rs2 : amo_alu_inputs.rs1_load;
            AMO_MINU_FN5 : result = rs1_smaller_than_rs2 ? amo_alu_inputs.rs1_load : amo_alu_inputs.rs2;
            AMO_MAXU_FN5 : result = rs1_smaller_than_rs2 ? amo_alu_inputs.rs2 : amo_alu_inputs.rs1_load;
        endcase
    end
    /* verilator lint_on CASEINCOMPLETE */


endmodule