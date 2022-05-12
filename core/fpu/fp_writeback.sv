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
 *             Yuhui Gao <yuhuig@sfu.ca>
 */

module fp_writeback
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import fpu_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter int unsigned NUM_UNITS [FP_NUM_WB_GROUPS] = '{3},
        parameter int unsigned NUM_WB_UNITS = 3
        //parameter int unsigned EXPO_WIDTH = EXPO_WIDTH, 
        //parameter int unsigned FRAC_WIDTH = FRAC_WIDTH,
        //parameter int unsigned FLEN = 1 + EXPO_WIDTH + FRAC_WIDTH 
    )

    (
        input logic clk,
        input logic rst,
        //Unit writeback
        fp_unit_writeback_interface.wb unit_wb[NUM_WB_UNITS],
        //WB output
        output fp_wb_packet_t wb_packet [FP_NUM_WB_GROUPS],
        //FCSR output
        output fflags_writeback_t fflags_wb_packet,
        //Snoop interface (LS unit)
        output fp_wb_packet_t wb_snoop
    );

    //Writeback
    //aliases for write-back-interface signals
    logic [NUM_WB_UNITS-1:0] unit_ack [FP_NUM_WB_GROUPS];
    id_t [NUM_WB_UNITS-1:0] unit_instruction_id [FP_NUM_WB_GROUPS];
    logic [NUM_WB_UNITS-1:0] unit_done [FP_NUM_WB_GROUPS];
    typedef logic [FLEN-1:0] unit_rd_t [NUM_WB_UNITS];
    unit_rd_t unit_rd [FP_NUM_WB_GROUPS];
    typedef logic [4:0] unit_fflags_t [NUM_WB_UNITS];
    unit_fflags_t unit_fflags [FP_NUM_WB_GROUPS];

    //Per-ID muxes for commit buffer
    logic [$clog2(NUM_WB_UNITS)-1:0] unit_sel [FP_NUM_WB_GROUPS];

    typedef int unsigned unit_count_t [FP_NUM_WB_GROUPS];
    function unit_count_t get_cumulative_unit_count();
    unit_count_t counts;
    int unsigned cumulative_count = 0;
    for (int i = 0; i < FP_NUM_WB_GROUPS; i++) begin
        counts[i] = cumulative_count;
        cumulative_count += NUM_UNITS[i];
    end
    return counts;
    endfunction
    localparam unit_count_t CUMULATIVE_NUM_UNITS = get_cumulative_unit_count();
  
    genvar i, j, k;
    ////////////////////////////////////////////////////
    //Implementation
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate
        for (i = 0; i < FP_NUM_WB_GROUPS; i++) begin
            for (j = 0; j < NUM_UNITS[i]; j++) begin
                assign unit_instruction_id[i][j] = unit_wb[CUMULATIVE_NUM_UNITS[i] + j].id;
                assign unit_done[i][j] = unit_wb[CUMULATIVE_NUM_UNITS[i] + j].done;
                assign unit_wb[CUMULATIVE_NUM_UNITS[i] + j].ack = unit_ack[i][j];
            end
        end
    endgenerate

    //As units are selected for commit ports based on their unit ID,
    //for each additional commit port one unit can be skipped for the commit mux
    generate
        for (i = 0; i < FP_NUM_WB_GROUPS; i++) begin
            for (j = 0; j < NUM_UNITS[i]; j++) begin
                assign unit_rd[i][j] = unit_wb[CUMULATIVE_NUM_UNITS[i] + j].rd;
                assign unit_fflags[i][j] = unit_wb[CUMULATIVE_NUM_UNITS[i] + j].fflags;
            end
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Unit select for register file
    //Iterating through all commit ports:
    //Search for complete units (in fixed unit order)
    //Assign to a commit port, mask that unit and commit port
    generate for (i = 0; i < FP_NUM_WB_GROUPS; i++) begin
        priority_encoder
            #(.WIDTH(NUM_UNITS[i]))
        unit_done_encoder
        (
            .priority_vector (unit_done[i][NUM_UNITS[i]-1 : 0]),
            .encoded_result (unit_sel[i][NUM_UNITS[i] == 1 ? 0 : ($clog2(NUM_UNITS[i])-1) : 0])
        );
    end endgenerate

    always_comb begin
        for (int i = 0; i < FP_NUM_WB_GROUPS; i++) begin
            wb_packet[i].valid = |unit_done[i];
            wb_packet[i].id = unit_instruction_id[i][unit_sel[i]];
            wb_packet[i].data = unit_rd[i][unit_sel[i]];

            //Unit Ack
            unit_ack[i] = '0;
            unit_ack[i][unit_sel[i]] = wb_packet[i].valid;

            //fflags output
            fflags_wb_packet.valid = wb_packet[i].valid;
            fflags_wb_packet.id = wb_packet[i].id;
            fflags_wb_packet.fflags = unit_fflags[i][unit_sel[i]];
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
            wb_snoop.valid <= wb_packet[0].valid;
    end
    always_ff @ (posedge clk) begin
        wb_snoop.data <= wb_packet[0].data;
        wb_snoop.id <= wb_packet[0].id;
    end
    
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    
    ////////////////////////////////////////////////////
    //simulation 
    //track writeback ack logic
    //logic multiple_done;
    //assign multiple_done = (|unit_done[0]) ? ~$onehot(unit_done[0]) : 0;

endmodule
