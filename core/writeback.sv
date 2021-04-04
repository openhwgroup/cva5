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

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    
    (
        input logic clk,
        input logic rst,
        //Unit writeback
        unit_writeback_interface.wb unit_wb[NUM_WB_UNITS],
        //WB output
        output wb_packet_t wb_packet [NUM_WB_GROUPS],
        //Snoop interface (LS unit)
        output wb_packet_t wb_snoop
    );

    //Writeback
    logic [NUM_WB_UNITS-1:0] unit_ack [NUM_WB_GROUPS];
    //aliases for write-back-interface signals
    id_t [NUM_WB_UNITS-1:0] unit_instruction_id [NUM_WB_GROUPS];
    logic [NUM_WB_UNITS-1:0] unit_done [NUM_WB_GROUPS];

    typedef logic [XLEN-1:0] unit_rd_t [NUM_WB_UNITS];
    unit_rd_t unit_rd [NUM_WB_GROUPS];
    //Per-ID muxes for commit buffer
    logic [$clog2(NUM_WB_UNITS)-1:0] unit_sel [NUM_WB_GROUPS];

    genvar i, j;
    ////////////////////////////////////////////////////
    //Implementation
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate
        for (i = 0; i < NUM_WB_GROUPS; i++) begin
            for (j = 0; j < NUM_WB_UNITS_GROUP[i]; j++) begin
                assign unit_instruction_id[i][j] = unit_wb[CUMULATIVE_NUM_WB_UNITS_GROUP[i] + j].id;
                assign unit_done[i][j] = unit_wb[CUMULATIVE_NUM_WB_UNITS_GROUP[i] + j].done;
                assign unit_wb[CUMULATIVE_NUM_WB_UNITS_GROUP[i] + j].ack = unit_ack[i][j];
            end
        end
    endgenerate

    //As units are selected for commit ports based on their unit ID,
    //for each additional commit port one unit can be skipped for the commit mux
    generate
        for (i = 0; i < NUM_WB_GROUPS; i++) begin
            for (j = 0; j < NUM_WB_UNITS_GROUP[i]; j++) begin
                assign unit_rd[i][j] = unit_wb[CUMULATIVE_NUM_WB_UNITS_GROUP[i] + j].rd;
            end
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Unit select for register file
    //Iterating through all commit ports:
    //   Search for complete units (in fixed unit order)
    //   Assign to a commit port, mask that unit and commit port
    generate for (i = 0; i < NUM_WB_GROUPS; i++) begin
        priority_encoder
            #(.WIDTH(NUM_WB_UNITS_GROUP[i]))
        unit_done_encoder
        (
            .priority_vector (unit_done[i][NUM_WB_UNITS_GROUP[i]-1 : 0]),
            .encoded_result (unit_sel[i][NUM_WB_UNITS_GROUP[i] == 1 ? 0 : ($clog2(NUM_WB_UNITS_GROUP[i])-1) : 0])
        );
        assign wb_packet[i].valid = |unit_done[i];
        assign wb_packet [i].id = unit_instruction_id[i][unit_sel[i]];
        assign wb_packet[i].data = unit_rd[i][unit_sel[i]];
    end endgenerate

    always_comb begin
        for (int i = 0; i < NUM_WB_GROUPS; i++) begin
            unit_ack[i] = '0;
            unit_ack[i][unit_sel[i]] = wb_packet[i].valid;
        end
    end

    ////////////////////////////////////////////////////
    //Store Forwarding Support
    //TODO: support additional writeback groups
    //currently limited to one writeback group with the
    //assumption that writeback group zero has single-cycle
    //operation
    always_ff @ (posedge clk) begin
        if (rst)
            wb_snoop.valid <= 0;
        else
            wb_snoop.valid <= wb_packet[1].valid;
    end
    always_ff @ (posedge clk) begin
        wb_snoop.data <= wb_packet[1].data;
        wb_snoop.id <= wb_packet[1].id;
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
