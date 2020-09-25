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

module register_file_and_writeback
    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    (
        input logic clk,
        input logic rst,

        //Issue interface
        input issue_packet_t issue,
        input logic alu_issued,
        output logic [31:0] rs_data [REGFILE_READ_PORTS],
        //ID Metadata
        output id_t ids_retiring [COMMIT_PORTS],
        output logic retired [COMMIT_PORTS],
        input logic [4:0] retired_rd_addr [COMMIT_PORTS],
        input id_t id_for_rd [COMMIT_PORTS],
        //Writeback
        unit_writeback_interface.wb unit_wb[NUM_WB_UNITS],
        output wb_packet_t wb_snoop,

        //Trace signals
        output logic tr_rs1_forwarding_needed,
        output logic tr_rs2_forwarding_needed,
        output logic tr_rs1_and_rs2_forwarding_needed
    );

    //Register File
    typedef logic [XLEN-1:0] register_file_t [32];
    register_file_t register_file [COMMIT_PORTS];
    logic [LOG2_COMMIT_PORTS-1:0] rs_sel [REGFILE_READ_PORTS];

    //Writeback
    logic alu_selected;
    logic [NUM_WB_UNITS-1:0] unit_ack [NUM_WB_GROUPS];
    //aliases for write-back-interface signals
    id_t [NUM_WB_UNITS-1:0] unit_instruction_id [NUM_WB_GROUPS];
    logic [NUM_WB_UNITS-1:0] unit_done [NUM_WB_GROUPS];


    typedef logic [XLEN-1:0] unit_rd_t [NUM_WB_UNITS];
    unit_rd_t unit_rd [NUM_WB_GROUPS];
    //Per-ID muxes for commit buffer
    logic [$clog2(NUM_WB_UNITS)-1:0] retiring_unit_select [NUM_WB_GROUPS];
    logic [31:0] retiring_data [NUM_WB_GROUPS];

    typedef logic [31:0] rs_data_set_t [REGFILE_READ_PORTS];
    rs_data_set_t rs_data_set [NUM_WB_GROUPS];

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
        for (i = 0; i < NUM_WB_GROUPS; i++) begin : wb_rd_mux_gen
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
    always_comb begin
        for (int i = 0; i < NUM_WB_GROUPS; i++) begin
            unit_ack[i] = '{default: 0};
            retired[i] = 0;
            retiring_unit_select[i] = WB_UNITS_WIDTH'(NUM_WB_UNITS_GROUP[i]-1);
            for (int j = 0; j < (NUM_WB_UNITS_GROUP[i] - 1); j++) begin
                if (unit_done[i][j]) begin
                    retiring_unit_select[i] = WB_UNITS_WIDTH'(j);
                    break;
                end
            end
            //ID and data muxes
            retired[i] = unit_done[i][retiring_unit_select[i]];
            ids_retiring[i] = unit_instruction_id[i][retiring_unit_select[i]];
            retiring_data[i] = unit_rd[i][retiring_unit_select[i]];
            unit_ack[i][retiring_unit_select[i]] = retired[i];
        end
        
        retired[0] = alu_issued;
        unit_ack[0][retiring_unit_select[0]] = retired[0];
    
    end

    ////////////////////////////////////////////////////
    //Register Files
    //Implemented in seperate module as there is not universal tool support for inferring
    //arrays of memory blocks.
    generate for (i = 0; i < COMMIT_PORTS; i++) begin
        register_file #(.NUM_READ_PORTS(REGFILE_READ_PORTS)) register_file_blocks (
            .clk, .rst,
            .rd_addr(retired_rd_addr[i]),
            .new_data(retiring_data[i]),
            .commit(update_lvt[i] & (|retired_rd_addr[i])),
            .read_addr(issue.rs_addr),
            .data(rs_data_set[i])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Register File LVT

    //Only update lvt if the retiring instrucion is the most recently issued
    //write to a given register.  This check allows multiple oustanding writes
    //to the same register.  As instructions can complete out-of-order, only
    //the most recently issued write to any given register will be committed
    logic update_lvt [COMMIT_PORTS];
    always_comb begin
        update_lvt[0] = retired[0];// & (alu_selected ? alu_issued : (id_for_rd[0] == ids_retiring[0]));
        for (int i = 1; i < COMMIT_PORTS; i++)
            update_lvt[i] = retired[i] & (id_for_rd[i] == ids_retiring[i]) & ~(retired[0] & retired_rd_addr[0] == retired_rd_addr[i]);
    end

    regfile_bank_sel regfile_lvt (
        .clk, .rst,
        .rs_addr(issue.rs_addr),
        .rs_sel,
        .rd_addr(retired_rd_addr),
        .rd_retired(update_lvt)
    );

    ////////////////////////////////////////////////////
    //Register File Muxing
    always_comb begin
        for (int i = 0; i < REGFILE_READ_PORTS; i++) begin
            rs_data[i] = rs_data_set[rs_sel[i]][i];
        end
    end

    ////////////////////////////////////////////////////
    //Store Forwarding Support
    always_ff @ (posedge clk) begin
        if (rst)
            wb_snoop.valid <= 0;
        else
            wb_snoop.valid <= retired[1];
    end
    always_ff @ (posedge clk) begin
        wb_snoop.data <= retiring_data[1];
        wb_snoop.id <= ids_retiring[1];
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
