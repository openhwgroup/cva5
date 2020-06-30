/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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
 *  FIFOs Not underflow/overflow safe.
 *  Intended for small FIFO depths.
 *  For continuous operation when full, enqueing side must inspect pop signal
 */
module taiga_fifo
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    #(
        parameter DATA_WIDTH = 70, 
        parameter FIFO_DEPTH = 4
    )
    (
        input logic clk,
        input logic rst,
        fifo_interface.structure fifo
    );

    localparam LOG2_FIFO_DEPTH = $clog2(FIFO_DEPTH);
    ////////////////////////////////////////////////////
    //Implementation
    //If depth is one, the FIFO can be implemented with a single register
    generate if (FIFO_DEPTH == 1) begin
        always_ff @ (posedge clk) begin
            if (rst)
                fifo.valid <= 0;
            else
                fifo.valid <= fifo.push | (fifo.valid & ~fifo.pop);
        end
        assign fifo.full = fifo.valid;

        always_ff @ (posedge clk) begin
            if (fifo.potential_push)
                fifo.data_out <= fifo.data_in;
        end
    end
    //If depth is two, the FIFO can be implemented with two registers
    //connected as a shift reg for the same resources as a LUTRAM FIFO
    //but with better timing
    else if (FIFO_DEPTH == 2) begin
        logic [DATA_WIDTH-1:0] shift_reg [FIFO_DEPTH];
        logic [LOG2_FIFO_DEPTH:0] inflight_count;
        ////////////////////////////////////////////////////
        //Occupancy Tracking
        always_ff @ (posedge clk) begin
            if (rst)
                inflight_count <= 0;
            else
                inflight_count <= inflight_count + (LOG2_FIFO_DEPTH+1)'(fifo.pop) - (LOG2_FIFO_DEPTH+1)'(fifo.push);
        end

        assign fifo.valid = inflight_count[LOG2_FIFO_DEPTH];
        assign fifo.full = fifo.valid & ~|inflight_count[LOG2_FIFO_DEPTH-1:0];

        always_ff @ (posedge clk) begin
            if (fifo.push) begin
                shift_reg[0] <= fifo.data_in;
                shift_reg[1] <= shift_reg[0];
            end
        end

        assign fifo.data_out = shift_reg[~inflight_count[0]];
    end
    else begin
        //Force FIFO depth to next power of 2
        (* ramstyle = "MLAB, no_rw_check" *) logic [DATA_WIDTH-1:0] lut_ram [(2**LOG2_FIFO_DEPTH)];
        logic [LOG2_FIFO_DEPTH-1:0] write_index;
        logic [LOG2_FIFO_DEPTH-1:0] read_index;
        logic [LOG2_FIFO_DEPTH:0] inflight_count;
        ////////////////////////////////////////////////////
        //Occupancy Tracking
        always_ff @ (posedge clk) begin
            if (rst)
                inflight_count <= 0;
            else
                inflight_count <= inflight_count + (LOG2_FIFO_DEPTH+1)'(fifo.pop) - (LOG2_FIFO_DEPTH+1)'(fifo.push);
        end

        assign fifo.valid = inflight_count[LOG2_FIFO_DEPTH];
        assign fifo.full = fifo.valid & ~|inflight_count[LOG2_FIFO_DEPTH-1:0];

        always_ff @ (posedge clk) begin
            if (rst) begin
                read_index <= '0;
                write_index <= '0;
            end
            else begin
                read_index <= read_index + LOG2_FIFO_DEPTH'(fifo.pop);
                write_index <= write_index + LOG2_FIFO_DEPTH'(fifo.push);
            end
        end

        always_ff @ (posedge clk) begin
            if (fifo.potential_push)
                lut_ram[write_index] <= fifo.data_in;
        end
        assign fifo.data_out = lut_ram[read_index];
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Assertions
    fifo_overflow_assertion:
        assert property (@(posedge clk) disable iff (rst) fifo.push |-> (~fifo.full | fifo.pop)) else $error("overflow");
    fifo_underflow_assertion:
        assert property (@(posedge clk) disable iff (rst) fifo.pop |-> fifo.valid) else $error("underflow");

endmodule