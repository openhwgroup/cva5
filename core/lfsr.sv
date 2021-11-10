/*
 * Copyright © 2021 Eric Matthews

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

//3-16 bit LFSRs with additional feedback to support full 2^N range
module lfsr

    #(
        parameter WIDTH = 3,
        parameter FULL_RANGE = 1
    )
    (
        input logic clk,
        input logic rst,
        input logic en,
        output logic [WIDTH-1:0] value
    );

    //Workaround for verilator: index in multi-dimensional array interpreted as non-constant
    //thus pulled out into separate array here
    localparam integer NUM_TAPS [14] = '{
        2, //3
        2, //4
        2,
        2,
        2,
        4, //8
        2,
        2,
        2,
        4, //12
        4,
        4,
        2, //15
        4 //16
    };

    //XNOR taps for LFSR from 3-16 bits wide (source: Xilinx xapp052)
    //tap index 1-N
    //Structure:
    //   Num-taps,   list of up-to 4 taps
    localparam integer TAPS [14][5] = '{
        '{2,  3,2,0,0}, //3
        '{2,  4,3,0,0}, //4
        '{2,  5,3,0,0},
        '{2,  6,5,0,0},
        '{2,  7,6,0,0},
        '{4,  8,6,5,4}, //8
        '{2,  9,5,0,0},
        '{2,  10,7,0,0},
        '{2,  11,9,0,0},
        '{4,  12,6,4,1}, //12
        '{4,  13,4,3,1},
        '{4,  14,5,3,1},
        '{2,  15,14,0,0}, //15
        '{4,  16,15,13,4} //16
    };

    //Min-width is 3
    localparam TAPS_INDEX = WIDTH - 3;

    logic [NUM_TAPS[TAPS_INDEX]-1:0] feedback_input;
    logic feedback;
    ////////////////////////////////////////////////////
    //Implementation

    generate begin
        for (genvar i = 0; i < NUM_TAPS[TAPS_INDEX]; i++) begin
            assign feedback_input[i] = value[TAPS[TAPS_INDEX][i + 1] - 1];
        end
        //XNOR of taps and range extension to include all ones
        if (FULL_RANGE)
            assign feedback = (~^feedback_input) ^ |value[WIDTH-2:0];
        else
            assign feedback = (~^feedback_input);
    end endgenerate

    initial value = 0;
    always_ff @ (posedge clk) begin
        if (en)
            value <= {value[WIDTH-2:0], feedback};
    end

endmodule
