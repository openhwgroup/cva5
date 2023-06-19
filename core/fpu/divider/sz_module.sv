/*
 * Copyright © 2023 Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

module sz_module
#(
    parameter WIDTH = 32
)
(
    input logic[WIDTH-1:0] ws,
    input logic[WIDTH-1:0] wc,
    output logic sign,
    output logic zero
);

    //Note that this implementation uses an adder
    //The alternative is a tree of generate/propagate blocks (see page 265 of "Digital Arithmetic" by Ercegovac and Lang)
    //For a 55 bit width, both have very similar delays but the tree uses slightly more resources

    logic[WIDTH-1:0] sum;
    assign sum = ws + wc;

    assign sign = sum[WIDTH-1];
    assign zero = ~|sum;

endmodule