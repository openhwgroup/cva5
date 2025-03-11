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
    if (WIDTH > 14)
        $error("Max priority encoder width exceeded!");

    //Tool workaround
    localparam MIN_WIDTH = (WIDTH == 1) ? 2 : WIDTH;
    localparam LOG2_WIDTH = $clog2(MIN_WIDTH);
    //Table generation for priority encoder
    function [2**MIN_WIDTH-1:0][LOG2_WIDTH-1 : 0] table_gen ();
        for (int i = 0; i < 2**MIN_WIDTH; i++) begin //Loop through all memory addresses
            table_gen[i] = LOG2_WIDTH'(MIN_WIDTH - 1);//Initialize to lowest priority
            for (int j = (int'(MIN_WIDTH) - 2); j >= 0; j--) begin//Check each bit in increasing priority
                if (i[j])//If bit is set update table value with that bit's index
                    table_gen[i] = LOG2_WIDTH'(j);
            end
        end
    endfunction

    //Initialize Table
    localparam logic [2**MIN_WIDTH-1:0][LOG2_WIDTH-1 : 0] ENCODER_ROM = table_gen();

    ////////////////////////////////////////////////////
    //Implementation
    assign encoded_result = (WIDTH == 1) ? 0 : ENCODER_ROM[priority_vector];

endmodule
