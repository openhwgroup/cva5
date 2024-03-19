/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

module barrel_shifter

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    
    (
        input logic[31:0] shifter_input,
        input logic[4:0] shift_amount,
        input logic arith,
        input logic lshift,
        output logic[31:0] shifted_result
        );

    logic [62:0] shift_in;
    logic [4:0] adjusted_shift_amount;
    ////////////////////////////////////////////////////
    //Implementation
    //Performs a 63-bit right shift
    //Left shift is handled by placing the left shift in the upper portion shifted by (~shift_amount + 1)
    //with the value initially shifted by one so that only the complement of the shift_amount is needed
    assign shift_in = lshift ? {shifter_input, 31'b0} : {{31{arith}}, shifter_input};
    assign adjusted_shift_amount = shift_amount ^ {5{lshift}};
    assign shifted_result = 32'(shift_in >> adjusted_shift_amount);
endmodule
