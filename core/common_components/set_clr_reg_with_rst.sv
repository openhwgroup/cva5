/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
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


 /*
  * Two varients are offered, one with set having precedence over clear and
  * vice versa.
  */
module set_clr_reg_with_rst

    import cva5_config::*;
    import cva5_types::*;

    #(parameter SET_OVER_CLR = 0, parameter WIDTH = 16, parameter logic[WIDTH-1:0] RST_VALUE = '0)
    (
        input logic clk,
        input logic rst,

        input logic [WIDTH-1:0] set,
        input logic [WIDTH-1:0] clr,
        output logic [WIDTH-1:0] result
    );

    ////////////////////////////////////////////////////
    //Implementation
    generate if (SET_OVER_CLR) begin : gen_set_over_clear
        always_ff @ (posedge clk) begin
            if (rst)
                result <= RST_VALUE;
            else
                result <= set | (result & ~clr);
        end
    end else begin : gen_clear_over_set
        always_ff @ (posedge clk) begin
            if (rst)
                result <= RST_VALUE;
            else
                result <= (set | result) & ~clr;
        end
    end
    endgenerate

endmodule
