/*
 * Copyright © 2021 Eric Matthews,  Lesley Shannon
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

////////////////////////////////////////////////////
//Highest Priority for: Index Zero
//Look-up Table based
//Max width of 12
////////////////////////////////////////////////////
module priority_encoder
    #(
        parameter WIDTH = 4
    )
    (
        input logic [WIDTH-1:0] priority_vector,
        output logic [(WIDTH == 1) ? 0 : ($clog2(WIDTH)-1) : 0] encoded_result
    );
    ////////////////////////////////////////////////////
    //Width Check
    if (WIDTH > 12)
        $error("Max priority encoder width exceeded!");

    localparam LOG2_WIDTH = $clog2(WIDTH);
    ////////////////////////////////////////////////////
    //Implementation

    generate
        if (WIDTH == 1)
            assign encoded_result = 0;
        else begin

            //Table generation for priority encoder
            function [2**WIDTH-1:0][LOG2_WIDTH-1 : 0] table_gen ();
                for (int i = 0; i < 2**WIDTH; i++) begin //Loop through all memory addresses
                    table_gen[i] = LOG2_WIDTH'(WIDTH - 1);//Initialize to lowest priority
                    for (int j = (WIDTH - 2); j >= 0; j--) begin//Check each bit in increasing priority
                        if (i[j])//If bit is set update table value with that bit's index
                            table_gen[i] = LOG2_WIDTH'(j);
                    end
                end
            endfunction

            //Initialize Table
            const logic [2**WIDTH-1:0][LOG2_WIDTH-1 : 0] encoder_rom = table_gen();

            assign encoded_result = encoder_rom[priority_vector];
        end
    endgenerate

endmodule
