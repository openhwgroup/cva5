/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

        input logic inorder,
        unit_writeback_interface.writeback unit_wb[NUM_WB_UNITS-1:0],
        register_file_writeback_interface.writeback rf_wb,
        inflight_queue_interface.wb iq,
        id_generator_interface.wb id_gen,
        id_table_interface.wb idt,
        output logic instruction_complete
        );

    logic done [NUM_WB_UNITS-1:0];
    logic early_done [NUM_WB_UNITS-1:0];
    logic [$clog2(INFLIGHT_QUEUE_DEPTH)-1:0] unit_ids [NUM_WB_UNITS-1:0];

    logic accepted [NUM_WB_UNITS-1:0];
    logic [XLEN-1:0] rd [NUM_WB_UNITS-1:0];

    logic not_in_queue;
    logic [4:0] rd_addr, rd_addr_r;
    logic [WB_UNITS_WIDTH-1:0] unit_id, unit_id_r;
    logic [$clog2(INFLIGHT_QUEUE_DEPTH)-1:0] iq_index, iq_index_corrected, iq_index_r;
    instruction_id_t issue_id, issue_id_r;

    logic [INFLIGHT_QUEUE_DEPTH-1:0] id_early_done, id_done, id_done_r;

    always_comb begin
        for (int i = 0; i < INFLIGHT_QUEUE_DEPTH; i++) begin
            id_early_done[i]=0;
            for (int j = 0; j < NUM_WB_UNITS; j++) begin
                id_early_done[i] |= early_done[j] && (unit_ids[j] == i);
            end
        end
    end

    genvar i;
    generate
        for (i=0; i<INFLIGHT_QUEUE_DEPTH; i++) begin : id_r
            always_ff @(posedge clk) begin
                if (rst | (issue_id == i))
                    id_done_r[i]  <= 0;
                else if (id_early_done[i])
                    id_done_r[i] <= 1;
            end
        end
    endgenerate

    assign id_done = id_early_done | id_done_r;
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate
    for (i=0; i< NUM_WB_UNITS; i++) begin : interface_to_array_g
        assign done[i] = unit_wb[i].done;
        assign early_done[i] = unit_wb[i].early_done;
        assign rd[i] = unit_wb[i].rd;
        assign unit_ids[i] = unit_wb[i].id;
        assign unit_wb[i].accepted = accepted[i];
    end
    endgenerate

    //Unit output selection.  Oldest unit with instruction complete if in out-of-order mode, otherwise oldest unit
    always_comb begin
        //queue input
        not_in_queue = 1;
        issue_id = iq.data_in.id;
        iq_index = 0;

        //queue outputs
        for (int i=0; i<INFLIGHT_QUEUE_DEPTH; i++) begin
            if ( (inorder | (~inorder & id_done[iq.data_out[i].id]))) begin //if inorder set find oldest valid instruction, otherwise find oldest instruction that is done
                not_in_queue = 0;
                issue_id = iq.data_out[i].id;
                iq_index = i;
            end
        end
    end

    assign idt.wb_instruction_id = issue_id;
    assign unit_id = not_in_queue ? iq.data_in.unit_id : idt.wb_unit_id;
    assign rd_addr = not_in_queue ? iq.data_in.rd_addr : idt.wb_rd_addr;

    always_ff @(posedge clk) begin
        if (rst)
            instruction_complete <= 0;
        else
            instruction_complete <= id_done[issue_id];
    end

    //As we decide our popping logic one cycle in advance we have to perform a correction in some cases
    assign iq_index_corrected = (~not_in_queue & iq.shift_pop[iq_index]) ? iq_index + 1: iq_index;

    always_ff @(posedge clk) begin
        iq_index_r <= iq_index_corrected;
        unit_id_r <= unit_id;
        issue_id_r <= issue_id;
        rd_addr_r <= rd_addr;
    end

    //assign instruction_complete = unit_wb.done[unit_id];//iq.data_out[iq_index].valid & unit_wb.done[unit_id];

    assign rf_wb.rd_addr =  rd_addr_r;
    assign rf_wb.id =  issue_id_r;

    assign rf_wb.rd_data = rd[unit_id_r];
    assign rf_wb.valid_write = instruction_complete;

    assign rf_wb.rd_addr_early =  rd_addr;
    assign rf_wb.id_early =  issue_id;
    assign rf_wb.valid_write_early = id_done[issue_id];

    generate
        for (i=0; i<INFLIGHT_QUEUE_DEPTH; i++) begin : iq_pop
            always_ff @(posedge clk) begin
                if (rst)
                    iq.pop[i]  <= 0;
                else
                    iq.pop[i] <= id_done[issue_id] && (iq_index_corrected == i);
            end
        end
    endgenerate

    generate
        for (i=0; i<NUM_WB_UNITS; i++) begin : wb_mux
            always_ff @(posedge clk) begin
                if (rst)
                    accepted[i] <= 0;
                else
                    accepted[i] <= id_done[issue_id] && (unit_id == i);
            end
        end
    endgenerate

    //ID generator signals
    assign id_gen.complete = instruction_complete;
    assign id_gen.complete_id = issue_id_r;
endmodule
