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
        output logic instruction_complete
        );

    logic [NUM_WB_UNITS-1:0] done_on_first_cycle;
    logic [NUM_WB_UNITS-1:0] done_next_cycle;

    logic selected_unit_done_next_cycle;
    logic entry_found;

    logic [NUM_WB_UNITS-1:0] accepted;
    logic [NUM_WB_UNITS-1:0] new_accepted;

    logic [XLEN-1:0] rd [NUM_WB_UNITS-1:0];

    logic [4:0] rd_addr, rd_addr_r;
    logic rd_addr_not_zero;
    logic [WB_UNITS_WIDTH-1:0] unit_id, unit_id_r;
    instruction_id_t issue_id, issue_id_r;
    int iq_index;

    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    genvar i;
    generate
        for (i=0; i< NUM_WB_UNITS; i++) begin : interface_to_array_g
            assign done_next_cycle[i] = unit_wb[i].done_next_cycle;
            assign done_on_first_cycle[i] = unit_wb[i].done_on_first_cycle;
            assign rd[i] = unit_wb[i].rd;
            assign unit_wb[i].accepted = accepted[i];
        end
    endgenerate

    //Unit output selection.  Oldest unit with instruction complete if in out-of-order mode, otherwise oldest unit
    //Done signals are same as early_done for all but ALU and Branch units.  If an ALU or BRANCH op is in the queue
    //it is already complete thus their done signals are registered to remove the combinational path through
    //issue logic.
    always_comb begin
        entry_found = 0;
        iq.pop = 0;
        selected_unit_done_next_cycle = 0;

        for (iq_index=INFLIGHT_QUEUE_DEPTH; iq_index>0; iq_index--) begin
            unit_id =  iq.data_out[iq_index].unit_id;

            if (iq.valid[iq_index]) begin
                selected_unit_done_next_cycle = done_next_cycle[unit_id];
                iq.pop[iq_index] = selected_unit_done_next_cycle;

                if (inorder | (~inorder & selected_unit_done_next_cycle)) begin
                    entry_found = 1;
                    break;
                end
            end
        end

        //No valid completing instructions in queue, check for new issues.
        if (~entry_found) begin
            unit_id = iq.data_out[0].unit_id;

            //Pop and unit done only if valid issue
            if (iq.valid[0]) begin
                selected_unit_done_next_cycle = done_on_first_cycle[unit_id];
                iq.pop[0] = selected_unit_done_next_cycle;
            end
        end

        issue_id = iq.data_out[iq_index].id;
        rd_addr = iq.data_out[iq_index].rd_addr;
        rd_addr_not_zero = iq.data_out[iq_index].rd_addr_nzero;
    end

    always_ff @(posedge clk) begin
        instruction_complete <= selected_unit_done_next_cycle;
    end

    always_ff @(posedge clk) begin
        unit_id_r <= unit_id;
        issue_id_r <= issue_id;
        rd_addr_r <= rd_addr;
    end

    assign rf_wb.rd_addr = rd_addr_r;
    assign rf_wb.id = issue_id_r;
    always_ff @(posedge clk) begin
            rf_wb.valid_write <= selected_unit_done_next_cycle & rd_addr_not_zero;
    end

    assign rf_wb.rd_data = rd[unit_id_r];

    always_comb begin
        new_accepted = 0;
        new_accepted[unit_id] = selected_unit_done_next_cycle;
    end

    always_ff @(posedge clk) begin
        accepted <= new_accepted;
    end

    //ID generator signals
    assign id_gen.complete = instruction_complete;
    assign id_gen.complete_id = issue_id_r;
endmodule
