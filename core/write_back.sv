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

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module write_back(
        input logic clk,
        input logic rst,

        input logic gc_fetch_flush,
        input logic instruction_issued_with_rd,

        unit_writeback_interface.wb unit_wb[NUM_WB_UNITS],
        register_file_writeback_interface.writeback rf_wb,

        output logic instruction_retired,
        output id_t retired_id,

        output logic single_cycle_issue_possible,
        output logic writeback_is_idle,

        //Trace signals
        output unit_id_t tr_num_instructions_completing,
        output id_t tr_num_instructions_in_flight,
        output id_t tr_num_of_instructions_pending_writeback
        );
    //////////////////////////////////////
    logic unit_ack [NUM_WB_UNITS];
    //aliases for write-back-interface signals
    id_t unit_instruction_id [NUM_WB_UNITS];
    logic unit_done [NUM_WB_UNITS];
    logic [XLEN-1:0] unit_rd [NUM_WB_UNITS];
    //Per-ID muxes for commit buffer
    logic [$clog2(NUM_WB_UNITS)-1:0] buffer_unit_select [WRITEBACK_BUFFERS];
    //Commit buffer
    typedef struct packed{
        logic [XLEN-1:0] rd;
        id_t id;
    } commit_buffer_t;
    commit_buffer_t commit_buffer [WRITEBACK_BUFFERS];
    logic commit_buffer_valid [WRITEBACK_BUFFERS];

    id_t id_retiring;

    localparam LOG2_WRITEBACK_BUFFERS = $clog2(WRITEBACK_BUFFERS);

    logic retiring;
    logic [$clog2(NUM_WB_UNITS):0] num_units_done;
    logic [$clog2(WRITEBACK_BUFFERS):0] num_buffers_ready;

    logic result_ready [WRITEBACK_BUFFERS];

    logic commit_buffer_ready [WRITEBACK_BUFFERS];

    logic [LOG2_WRITEBACK_BUFFERS-1:0] commit_buffer_index_retiring;

    genvar i, j;
    ////////////////////////////////////////////////////
    //Implementation
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate for (i=0; i< NUM_WB_UNITS; i++) begin : wb_interfaces_to_arrays_g
        assign unit_instruction_id[i] = unit_wb[i].id;
        assign unit_done[i] = unit_wb[i].done;
        assign unit_rd[i] = unit_wb[i].rd;
        assign unit_wb[i].ack = unit_ack[i];
    end endgenerate

    ////////////////////////////////////////////////////
    //Unit done determination
    always_comb begin
        num_units_done = 0;
        for (int i=0; i < NUM_MULTI_CYCLE_WB_UNITS; i++) begin
            num_units_done += ($clog2(NUM_WB_UNITS)+1)'(unit_done[i]);
        end
        num_buffers_ready = 0;
        for (int i=0; i < WRITEBACK_BUFFERS; i++) begin
            num_buffers_ready += ($clog2(WRITEBACK_BUFFERS)+1)'(commit_buffer_ready[i]);
        end
        single_cycle_issue_possible = (($clog2(NUM_WB_UNITS)+1)'(num_buffers_ready) > num_units_done);
    end

    ////////////////////////////////////////////////////
    //Commit Buffer index retiring
    //Priority given to decreasing indices
    always_comb begin
        commit_buffer_index_retiring = 0;
        for (int i=WRITEBACK_BUFFERS-1; i >= 0; i--) begin
            if (commit_buffer_valid[i])
                commit_buffer_index_retiring = LOG2_WRITEBACK_BUFFERS'(i);
        end
    end

    ////////////////////////////////////////////////////
    //Commit Buffer ready to accept new data
    always_comb begin
        for (int i=0; i < WRITEBACK_BUFFERS; i++) begin
            commit_buffer_ready[i] = ~commit_buffer_valid[i];
        end
        //Can always retire, so if not retiring, this index will not be valid and thus ready to commit to
        commit_buffer_ready[commit_buffer_index_retiring] = 1;
    end

    ////////////////////////////////////////////////////
    //Unit select for writeback buffer
    logic commit_buffer_write [WRITEBACK_BUFFERS];
    always_comb begin
        unit_ack = '{default: 0};
        buffer_unit_select = '{default: 0};
        commit_buffer_write = '{default: 0};
        for (int i=0; i < WRITEBACK_BUFFERS; i++) begin
            for (int j=0; j < NUM_WB_UNITS; j++) begin
                if (unit_done[j] & ~unit_ack[j] & ~commit_buffer_write[i]) begin
                    buffer_unit_select[i] = $clog2(NUM_WB_UNITS)'(j);
                    unit_ack[j] = commit_buffer_ready[i];
                    commit_buffer_write[i] = commit_buffer_ready[i];
                end
            end
        end
        // single_cycle_issue_possible = 0;
        // for (int i=0; i < WRITEBACK_BUFFERS; i++) begin
        //     if (commit_buffer_ready[i] & ~commit_buffer_write[i]) begin
        //         single_cycle_issue_possible = 1;
        //         buffer_unit_select[i] = ALU_UNIT_WB_ID;
        //         commit_buffer_write[i] = 1;
        //         break;
        //     end
        // end
    end

    ////////////////////////////////////////////////////
    //Writeback Commit Buffer
    always_ff @ (posedge clk) begin
        for (int i=0; i < WRITEBACK_BUFFERS; i++) begin
            if (rst)
                commit_buffer_valid[i] <= 0;
            else
                commit_buffer_valid[i] <= commit_buffer_write[i] | (commit_buffer_valid[i] & ~commit_buffer_ready[i]);
        end
    end

    always_ff @ (posedge clk) begin
        for (int i=0; i < WRITEBACK_BUFFERS; i++) begin
            if (commit_buffer_ready[i]) begin
                commit_buffer[i].rd <= unit_rd[buffer_unit_select[i]];
                commit_buffer[i].id <= unit_instruction_id[buffer_unit_select[i]];
            end
        end
    end

    ////////////////////////////////////////////////////
    //Register File Interface
    always_comb begin
        retiring = 0;
        for (int i=0; i < WRITEBACK_BUFFERS; i++) begin
            retiring |= commit_buffer_valid[i];
        end
    end

    assign id_retiring = commit_buffer[commit_buffer_index_retiring].id;

    //Instruction completion tracking for retired instruction count
    assign instruction_retired = retiring;
    assign retired_id = id_retiring;


    assign rf_wb.id = id_retiring;
    assign rf_wb.retiring = instruction_retired;
    assign rf_wb.rd_data = commit_buffer[commit_buffer_index_retiring].rd;

    //Register bypass for issue operands
    logic [WRITEBACK_BUFFERS-1:0] rs1_addr_match;
    logic [WRITEBACK_BUFFERS-1:0] rs2_addr_match;
    logic [LOG2_WRITEBACK_BUFFERS-1:0] rs1_sel;
    logic [LOG2_WRITEBACK_BUFFERS-1:0] rs2_sel;
    always_comb begin
        writeback_is_idle = 0;
        rs1_sel = {LOG2_WRITEBACK_BUFFERS{1'b?}};
        rs2_sel = {LOG2_WRITEBACK_BUFFERS{1'b?}};
        for (int i=0; i < WRITEBACK_BUFFERS; i++) begin
            writeback_is_idle |= commit_buffer_valid[i];
            rs1_addr_match[i] = commit_buffer_valid[i] && (commit_buffer[i].id == rf_wb.rs1_id);
            rs2_addr_match[i] = commit_buffer_valid[i] && (commit_buffer[i].id == rf_wb.rs2_id);
            if (rs1_addr_match[i])
                rs1_sel = LOG2_WRITEBACK_BUFFERS'(i);
            if (rs2_addr_match[i])
                rs2_sel = LOG2_WRITEBACK_BUFFERS'(i);
        end
        writeback_is_idle = ~writeback_is_idle;
    end

    assign rf_wb.rs1_valid = |rs1_addr_match;
    assign rf_wb.rs2_valid = |rs2_addr_match;
    assign rf_wb.rs1_data = commit_buffer[rs1_sel].rd;
    assign rf_wb.rs2_data = commit_buffer[rs2_sel].rd;
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
   //  instruction_id_t num_of_instructions_pending_writeback;
   // generate if (ENABLE_TRACE_INTERFACE) begin
       //Checks if any two pairs are set indicating mux contention
   //     always_comb begin
   //         tr_num_instructions_completing = 0;
   //         for (int i=0; i<NUM_WB_UNITS; i++) begin
   //             tr_num_instructions_completing += unit_done[i];
   //         end


   //         num_of_instructions_pending_writeback = 0;
   //         for (int i=0; i<MAX_INFLIGHT_COUNT-1; i++) begin
   //             num_of_instructions_pending_writeback += ID_W'(id_writeback_pending_r[i]);
   //         end
   //         tr_num_instructions_in_flight = tr_num_of_instructions_pending_writeback > 2 ? 2'b1 : 0;
   //     end
   // end
   // endgenerate

endmodule
