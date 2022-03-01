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
module register_free_list

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    
    #(
        parameter DATA_WIDTH = 70, 
        parameter FIFO_DEPTH = 4
    )
    (
        input logic clk,
        input logic rst,
        fifo_interface.structure fifo,
        input logic rollback
    );

    localparam LOG2_FIFO_DEPTH = $clog2(FIFO_DEPTH);

    //Force FIFO depth to next power of 2
    (* ramstyle = "MLAB, no_rw_check" *) logic [DATA_WIDTH-1:0] lut_ram [(2**LOG2_FIFO_DEPTH)];
    logic [LOG2_FIFO_DEPTH-1:0] write_index;
    logic [LOG2_FIFO_DEPTH-1:0] read_index;
    logic [LOG2_FIFO_DEPTH:0] inflight_count;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Occupancy Tracking
    always_ff @ (posedge clk) begin
        if (rst)
            inflight_count <= 0;
        else
            inflight_count <= inflight_count 
            + (LOG2_FIFO_DEPTH+1)'(fifo.pop) 
            - (LOG2_FIFO_DEPTH+1)'(fifo.push) 
            - (LOG2_FIFO_DEPTH+1)'(rollback);
    end

    assign fifo.valid = inflight_count[LOG2_FIFO_DEPTH];
    assign fifo.full = fifo.valid & ~|inflight_count[LOG2_FIFO_DEPTH-1:0];

    always_ff @ (posedge clk) begin
        if (rst) begin
            read_index <= '0;
            write_index <= '0;
        end
        else begin
            read_index <= read_index + LOG2_FIFO_DEPTH'(fifo.pop) - LOG2_FIFO_DEPTH'(rollback);
            write_index <= write_index + LOG2_FIFO_DEPTH'(fifo.push);
        end
    end

    always_ff @ (posedge clk) begin
        if (fifo.potential_push)
            lut_ram[write_index] <= fifo.data_in;
    end
    assign fifo.data_out = lut_ram[read_index];

    ////////////////////////////////////////////////////
    //Assertions
    fifo_overflow_assertion:
        assert property (@(posedge clk) disable iff (rst) fifo.push |-> (~fifo.full | fifo.pop)) else $error("overflow");
    fifo_underflow_assertion:
        assert property (@(posedge clk) disable iff (rst) fifo.pop |-> fifo.valid) else $error("underflow");

endmodule