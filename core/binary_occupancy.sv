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

module binary_occupancy

    import cva5_config::*;
    import cva5_types::*;
    
    #(parameter DEPTH = 4)
    (
        input logic clk,
        input logic rst,
        input logic push,
        input logic pop,
        output logic almost_full,
        output logic full,
        output logic empty,
        output logic almost_empty,
        output logic valid
    );

    logic[$clog2(DEPTH)-1:0] count;

    //Occupancy Tracking
    always_ff @ (posedge clk) begin
        if (rst)
            count <= 0;
        else begin
            case ({push, pop})
                2'b10: count <= count + 1;
                2'b01: count <= count - 1;
                default : count <= count;
            endcase
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            valid <= 0;
        else begin
            case ({push, pop})
                2'b10: valid <= 1;
                2'b01: valid <= !(count == 1);
                default : valid <= valid;
            endcase
        end
    end

    // always_ff @ (posedge clk) begin
    //     if (rst)
    //         full <= 0;
    //     else begin
    //         case ({push, pop})
    //             2'b10: full <= (count == DEPTH-2);
    //             2'b01: full <= 0;
    //             default : full <= full;
    //         endcase
    //     end
    // end

    // always_ff @ (posedge clk) begin
    //     if (rst)
    //         almost_full <= 0;
    //     else begin
    //         case ({push, pop})
    //             2'b10: almost_full <= (count == DEPTH-3);
    //             2'b01: almost_full <= (count == DEPTH-1);
    //             default : almost_full <= almost_full;
    //         endcase
    //     end
    // end

    // always_ff @ (posedge clk) begin
    //     if (rst)
    //         almost_empty <= 0;
    //     else begin
    //         case ({push, pop})
    //             2'b10: almost_empty <=(count == 0);
    //             2'b01: almost_empty <= (count == 2);
    //             default : almost_empty <= almost_empty;
    //         endcase
    //     end
    // end

    assign empty = ~valid;

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(~rst & full & push)) else $error("overflow");
        assert (!(~rst & empty & pop)) else $error("underflow");
    end

endmodule


