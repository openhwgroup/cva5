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

import taiga_config::*;
import taiga_types::*;

module write_back(
        input logic clk,
        input logic rst,

        input logic instruction_issued_with_rd,

        input unit_writeback_t unit_wb[NUM_WB_UNITS-1:0],
        register_file_writeback_interface.writeback rf_wb,
        tracking_interface.wb ti,
        output logic instruction_complete,
        output logic instruction_queue_empty,
        output instruction_id_t oldest_id,

        input instruction_id_t store_id,
        input instruction_id_t store_done_id,
        input logic store_complete,
        output logic [31:0] wb_buffer_data,
        output logic wb_buffer_data_valid,


        //Trace signals
        output logic tr_wb_mux_contention
        );
    //////////////////////////////////////

    //Inflight packetscd
    (* ramstyle = "MLAB, no_rw_check" *) logic[$bits(inflight_instruction_packet)-1:0] packet_table [MAX_INFLIGHT_COUNT-1:0];

    //aliases for write-back-interface signals
    instruction_id_t unit_instruction_id [NUM_WB_UNITS-1:0];
    logic [NUM_WB_UNITS-1:0] unit_done;
    logic [XLEN-1:0] unit_rd [NUM_WB_UNITS-1:0];
    /////

    logic [XLEN-1:0] rds_by_id [MAX_INFLIGHT_COUNT-1:0];
    logic [XLEN-1:0] rds_by_id_next [MAX_INFLIGHT_COUNT-1:0];

    logic [$clog2(NUM_WB_UNITS)-1:0] id_unit_select [MAX_INFLIGHT_COUNT-1:0];
    instruction_id_t issue_id, retired_id, retired_id_r;
    inflight_instruction_packet retired_instruction_packet;

    logic [MAX_INFLIGHT_COUNT-1:0] id_done;
    logic [MAX_INFLIGHT_COUNT-1:0] id_done_new;
    logic [MAX_INFLIGHT_COUNT-1:0] id_done_r;

    logic retired, retired_r;
    ////////////////////////////////////////////////////
    //Implementation

    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    genvar i;
    generate
        for (i=0; i< NUM_WB_UNITS; i++) begin : interface_to_array_g
            assign unit_instruction_id[i] = unit_wb[i].id;
            assign unit_done[i] = unit_wb[i].done;
            assign unit_rd[i] = unit_wb[i].rd;
        end
    endgenerate

    always_comb begin
        for (int i=0; i< MAX_INFLIGHT_COUNT; i++) begin
            id_done_new[i] = 0;
            id_unit_select[i] = 0;
            for (int j=0; j< NUM_WB_UNITS; j++) begin
                if (unit_done[j] && (unit_instruction_id[j] == i[$clog2(MAX_INFLIGHT_COUNT)-1:0])) begin
                    id_unit_select[i] = j[$clog2(NUM_WB_UNITS)-1:0];
                    id_done_new[i] |= 1;
                end
            end
            if (store_complete && store_done_id == i[$clog2(MAX_INFLIGHT_COUNT)-1:0])
                id_done_new[i] |= 1;
        end
    end

    generate
        for (i=0; i< MAX_INFLIGHT_COUNT; i++) begin
            assign rds_by_id_next[i] = unit_rd[id_unit_select[i]];
            always_ff @ (posedge clk) begin
                if (id_done_new[i])
                    rds_by_id[i] <= rds_by_id_next[i];
            end
        end
    endgenerate

    assign wb_buffer_data = rds_by_id[store_id];
    assign wb_buffer_data_valid = id_done_r[store_id];

    //ID tracking
    id_tracking id_fifos (.*, .issued(ti.issued), .retired(retired), .id_available(ti.id_available),
    .oldest_id(oldest_id), .next_id(issue_id), .empty(instruction_queue_empty));

    assign ti.issue_id = issue_id;

    initial begin
        foreach(packet_table[i])
        packet_table[i] = '0;
    end
    //Inflight Instruction ID table
    //Stores rd_addr and whether rd_addr is zero
    always_ff @ (posedge clk) begin
        if (ti.id_available)//instruction_issued_with_rd
            packet_table[issue_id] <= ti.inflight_packet;
    end

    always_ff @ (posedge clk) begin
        retired_instruction_packet <= instruction_queue_empty ? ti.inflight_packet : packet_table[retired_id];
    end
    //////////////////////

    //One-hot ID retired last cycle
    logic [MAX_INFLIGHT_COUNT-1:0] id_retired_last_cycle;
    logic [MAX_INFLIGHT_COUNT-1:0] id_retired_last_cycle_r;
    always_comb begin
        id_retired_last_cycle = 0;
        id_retired_last_cycle[retired_id] = retired;
    end

    always_ff @ (posedge clk) begin
        id_retired_last_cycle_r <= id_retired_last_cycle;
    end

    assign  id_done = (id_done_r & ~id_retired_last_cycle_r) | id_done_new;

    always_ff @ (posedge clk) begin
        if (rst)
            id_done_r <= '0;
        else
            id_done_r <= id_done;
    end

    assign retired = id_done[oldest_id];
    assign retired_id = oldest_id;

    always_ff @(posedge clk) begin
        retired_r <= retired;
        retired_id_r <= retired_id;
    end

    assign instruction_complete = retired_r & ~retired_instruction_packet.is_store;

    //Register file interaction
    assign rf_wb.rd_addr = retired_instruction_packet.rd_addr;
    assign rf_wb.id = retired_id_r;
    assign rf_wb.retired = instruction_complete;
    assign rf_wb.rd_nzero = retired_instruction_packet.rd_addr_nzero;
    assign rf_wb.rd_data = rds_by_id[retired_id_r];

    assign rf_wb.rs1_valid = id_done_r[rf_wb.rs1_id];
    assign rf_wb.rs2_valid = id_done_r[rf_wb.rs2_id];

    assign rf_wb.rs1_data = rds_by_id[rf_wb.rs1_id];
    assign rf_wb.rs2_data = rds_by_id[rf_wb.rs2_id];
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin
        //Checks if any two pairs are set indicating mux contention
        always_comb begin
            tr_wb_mux_contention = 0;
            for (int i=0; i<MAX_INFLIGHT_COUNT-1; i++) begin
                    for (int j=i+1; j<MAX_INFLIGHT_COUNT; j++) begin
                        tr_wb_mux_contention |= (id_done_r[i] & id_done_r[j]);
                    end
            end
        end
    end
    endgenerate

endmodule
