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

    logic [NUM_WB_UNITS-1:0] early_done;
    logic [NUM_WB_UNITS-1:0] done;

    logic selected_unit_done;
    logic entry_found;

    logic [NUM_WB_UNITS-1:0] accepted;
    logic [XLEN-1:0] rd [NUM_WB_UNITS-1:0];

    logic [4:0] rd_addr, rd_addr_r;
    logic [WB_UNITS_WIDTH-1:0] unit_id, unit_id_r;
    instruction_id_t issue_id, issue_id_r;


    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    genvar i;
    generate
        for (i=0; i< NUM_WB_UNITS; i++) begin : interface_to_array_g
            assign done[i] = unit_wb[i].done;
            assign early_done[i] = unit_wb[i].early_done;
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
        selected_unit_done = 0;

        for (int i=INFLIGHT_QUEUE_DEPTH; i>0; i--) begin
            unit_id =  iq.data_out[i].unit_id;
            issue_id = iq.data_out[i].id;

            if (iq.valid[i]) begin
                selected_unit_done = done[iq.data_out[i].unit_id];
                iq.pop[i] = done[iq.data_out[i].unit_id];

                if (inorder | (~inorder & done[iq.data_out[i].unit_id])) begin
                    entry_found = 1;
                    break;
                end
            end
        end

        //Access rd_addr table in inflight_queue
        iq.wb_id = issue_id;
        rd_addr = iq.wb_rd_addr;

        //No valid completing instructions in queue, check for new issues.
        if (~entry_found) begin
            unit_id = iq.data_out[0].unit_id;
            issue_id = iq.data_out[0].id;
            rd_addr = iq.future_rd_addr;
            //Pop and unit done only if valid issue
            selected_unit_done = early_done[iq.data_out[0].unit_id] & iq.valid[0];
            iq.pop[0] = early_done[iq.data_out[0].unit_id] &  iq.valid[0];
        end
    end

    always_ff @(posedge clk) begin
        if (rst)
            instruction_complete <= 0;
        else
            instruction_complete <= selected_unit_done;
    end

    always_ff @(posedge clk) begin
        unit_id_r <= unit_id;
        issue_id_r <= issue_id;
        rd_addr_r <= rd_addr;
    end

    assign rf_wb.rd_addr =  rd_addr_r;
    assign rf_wb.id =  issue_id_r;

    assign rf_wb.rd_data = rd[unit_id_r];
    always_ff @(posedge clk) begin
        if (rst)
            rf_wb.valid_write <= 0;
        else
            rf_wb.valid_write <= selected_unit_done && (rd_addr != 0);
    end

    assign rf_wb.rd_addr_early = rd_addr;
    assign rf_wb.id_early =  issue_id;
    assign rf_wb.valid_write_early = selected_unit_done;

    generate
        for (i=0; i<NUM_WB_UNITS; i=i+1) begin : wb_mux
            always_ff @(posedge clk) begin
                if (rst)
                    accepted[i] <= 0;
                else
                    accepted[i] <= selected_unit_done && (unit_id == i);
            end
        end
    endgenerate

    //ID generator signals
    assign id_gen.complete = instruction_complete;
    assign id_gen.complete_id = issue_id_r;
endmodule
