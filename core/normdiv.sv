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
               Alec Lu <alec_lu@sfu.ca>
 */

 module normdiv
        #(
        parameter C_WIDTH = 32,
        parameter DIV_TYPE = "radix-2"
        )
        (
        input logic clk,
        input logic rst,
        input logic start,
        input logic ack,
        input logic [C_WIDTH-1:0] A,
        input logic [C_WIDTH-1:0] B,
        output logic [C_WIDTH-1:0] Q,
        output logic [C_WIDTH-1:0] R,
        output logic complete
        );

    generate
        if (DIV_TYPE == "radix-2")
            div_radix2 #(C_WIDTH) div (.*);
        else if (DIV_TYPE == "radix-2_earlyTerminate")
            div_radix2_ET #(C_WIDTH) div (.*);
        else if (DIV_TYPE == "radix-2_earlyTerminate_full")
            div_radix2_ET_full #(C_WIDTH) div (.*);
        else if (DIV_TYPE == "radix-4")
            div_radix4 #(C_WIDTH) div (.*);
        else if (DIV_TYPE == "radix-4_earlyTerminate")
            div_radix4_ET #(C_WIDTH) div (.*);
        else if (DIV_TYPE == "radix-8")
            div_radix8 #(C_WIDTH) div (.*);
        else if (DIV_TYPE == "radix-16")
            div_radix16 #(C_WIDTH) div (.*);
        else
            div_radix2 #(C_WIDTH) div (.*);
    endgenerate

endmodule




