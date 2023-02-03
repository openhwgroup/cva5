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

module writeback

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    
    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter int unsigned NUM_WB_UNITS = 5
    )

    (
        input logic clk,
        input logic rst,
        //Unit writeback
        unit_writeback_interface.wb unit_wb[NUM_WB_UNITS],
        //WB output
        output wb_packet_t wb_packet
    );

    //Writeback
    logic [NUM_WB_UNITS-1:0] unit_ack;
    //aliases for write-back-interface signals
    id_t [NUM_WB_UNITS-1:0] unit_instruction_id;
    logic [NUM_WB_UNITS-1:0] unit_done;

    logic [XLEN-1:0] unit_rd [NUM_WB_UNITS];

    localparam int unsigned LOG2_NUM_WB_UNITS = NUM_WB_UNITS == 1 ? 1 : $clog2(NUM_WB_UNITS);
    //Per-ID muxes for commit buffer
    logic [LOG2_NUM_WB_UNITS-1:0] unit_sel;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate for (i = 0; i < NUM_WB_UNITS; i++) begin : gen_wb_unit_unpacking
        assign unit_instruction_id[i] = unit_wb[i].id;
        assign unit_done[i] = unit_wb[i].done;
        assign unit_wb[i].ack = unit_ack[i];
        assign unit_rd[i] = unit_wb[i].rd;
    end endgenerate

    ////////////////////////////////////////////////////
    //Unit select for register file
    //Iterating through all commit ports:
    //   Search for complete units (in fixed unit order)
    //   Assign to a commit port, mask that unit and commit port
    priority_encoder #(.WIDTH(NUM_WB_UNITS))
    unit_done_encoder
    (
        .priority_vector (unit_done),
        .encoded_result (unit_sel[LOG2_NUM_WB_UNITS -1 : 0])
    );
    assign wb_packet.valid = |unit_done;
    assign wb_packet.id = unit_instruction_id[unit_sel];
    assign wb_packet.data = unit_rd[unit_sel];

    assign unit_ack = NUM_WB_UNITS'(wb_packet.valid) << unit_sel;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule