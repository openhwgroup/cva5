/*
 * Copyright © 2017 Eric Matthews, Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module amo_alu

    import riscv_types::*;

    #(
        parameter int WIDTH = 32
    )
    (
        input amo_t amo_type,
        input logic[WIDTH-1:0] rs1,
        input logic[WIDTH-1:0] rs2,
        output logic[WIDTH-1:0] rd
    );

    logic signed_op;
    logic rs1_smaller_than_rs2;
    logic signed [WIDTH:0] rs1_ext;
    logic signed [WIDTH:0] rs2_ext;
    
    assign signed_op = amo_type == AMO_MIN_FN5 | amo_type == AMO_MAX_FN5;
    assign rs1_ext = {(signed_op & rs1[WIDTH-1]), rs1};
    assign rs2_ext = {(signed_op & rs2[WIDTH-1]), rs2};
    assign rs1_smaller_than_rs2 = rs1_ext < rs2_ext;

    always_comb begin
        unique case (amo_type)
            AMO_XOR_FN5 : rd = rs1 ^ rs2;
            AMO_OR_FN5 : rd = rs1 | rs2;
            AMO_AND_FN5 : rd = rs1 & rs2;
            AMO_SWAP_FN5 : rd = rs2;
            AMO_MIN_FN5 : rd = rs1_smaller_than_rs2 ? rs1 : rs2;
            AMO_MAX_FN5 : rd = rs1_smaller_than_rs2 ? rs2 : rs1;
            AMO_MINU_FN5 : rd = rs1_smaller_than_rs2 ? rs1 : rs2;
            AMO_MAXU_FN5 : rd = rs1_smaller_than_rs2 ? rs2 : rs1;
            AMO_ADD_FN5 : rd = rs1 + rs2;
            default : rd = 'x; //Default don't care allows some optimization
        endcase
    end

endmodule
