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
        parameter int unsigned WIDTH = 3,
        parameter NEEDS_RESET = 1
    )
    (
        input logic clk,
        input logic rst,
        input logic en,
        output logic [WIDTH-1:0] value
    );

    typedef struct packed {
        int unsigned NUM;
        bit [3:0][31:0] INDICIES;
    } tap_t;

    //XNOR taps for LFSR from 3-16 bits wide (source: Xilinx xapp052)
    localparam tap_t LFSR_TAPS [17] = '{
        //Dummy entries for widths 0-2
        '{NUM : 1,    INDICIES : '{0,0,0,0}},
        '{NUM : 1,    INDICIES : '{0,0,0,0}},
        '{NUM : 1,    INDICIES : '{0,0,0,0}}, 
        //Number of taps and indicies[3:0] for LFSRs width 3 to 16
        '{NUM : 2,    INDICIES : '{0,0,1,2}}, //3
        '{NUM : 2,    INDICIES : '{0,0,2,3}}, //4
        '{NUM : 2,    INDICIES : '{0,0,2,4}},
        '{NUM : 2,    INDICIES : '{0,0,4,5}},
        '{NUM : 2,    INDICIES : '{0,0,5,6}},
        '{NUM : 4,    INDICIES : '{3,4,5,7}}, //8
        '{NUM : 2,    INDICIES : '{0,0,4,8}},
        '{NUM : 2,    INDICIES : '{0,0,6,9}},
        '{NUM : 2,    INDICIES : '{0,0,8,10}},
        '{NUM : 4,    INDICIES : '{0,3,5,11}}, //12
        '{NUM : 4,    INDICIES : '{0,2,3,12}},
        '{NUM : 4,    INDICIES : '{0,2,4,13}},
        '{NUM : 2,    INDICIES : '{0,0,13,14}}, //15
        '{NUM : 4,    INDICIES : '{3,12,14,15}} //16
    };

    localparam tap_t TAPS = LFSR_TAPS[WIDTH];

    logic [TAPS.NUM-1:0] feedback_input;
    logic feedback;
    ////////////////////////////////////////////////////
    //Implementation
    generate if (WIDTH <= 2) begin : gen_width_one_or_two
        assign feedback = ~value[WIDTH-1];
    end
    else begin : gen_width_three_plus
        for (genvar i = 0; i < TAPS.NUM; i++) begin : gen_taps
            assign feedback_input[i] = value[int'(TAPS.INDICIES[i])];
        end
        //XNOR of taps and range extension to include all ones
        assign feedback = (~^feedback_input) ^ |value[WIDTH-2:0];
    end
    endgenerate

    initial value = 0;
    always_ff @ (posedge clk) begin
        if (NEEDS_RESET & rst)
            value <= '0;
        else if (en) begin
            value <= value << 1;
            value[0] <= feedback;
        end
    end

endmodule
