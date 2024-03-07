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
    import cva5_types::*;
    
    # (
        parameter int unsigned NUM_WB_UNITS = 5,
        parameter unit_id_enum_t [MAX_NUM_UNITS-1:0] WB_INDEX = '{0: ALU_ID, 1: MUL_ID, 2: DIV_ID, 3: LS_ID, 4: CSR_ID, 5: FPU_ID, default: NON_WRITEBACK_ID}
    )

    (
        //Unit writeback
        unit_writeback_interface.wb unit_wb[MAX_NUM_UNITS],
        //WB output
        output wb_packet_t wb_packet
    );

    //aliases for write-back-interface signals
    id_t [NUM_WB_UNITS-1:0] unit_instruction_id;
    logic [NUM_WB_UNITS-1:0] unit_done;
    logic [31:0] unit_rd [NUM_WB_UNITS];
    logic [NUM_WB_UNITS-1:0] unit_ack;

    localparam int unsigned LOG2_NUM_WB_UNITS = (NUM_WB_UNITS == 1) ? 1 : $clog2(NUM_WB_UNITS);
    logic [LOG2_NUM_WB_UNITS-1:0] unit_sel;

    ////////////////////////////////////////////////////
    //Implementation
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate for (genvar i = 0; i < NUM_WB_UNITS; i++) begin : gen_wb_unit_unpacking
        assign unit_instruction_id[i] = unit_wb[WB_INDEX[i]].id;
        assign unit_done[i] = unit_wb[WB_INDEX[i]].done;
        assign unit_rd[i] = unit_wb[WB_INDEX[i]].rd;
        assign unit_wb[WB_INDEX[i]].ack = unit_ack[i];
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
        .encoded_result (unit_sel)
    );
    assign wb_packet = '{
        valid : |unit_done,
        id : unit_instruction_id[unit_sel],
        data : unit_rd[unit_sel]
    };

    assign unit_ack = NUM_WB_UNITS'(wb_packet.valid) << unit_sel;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
