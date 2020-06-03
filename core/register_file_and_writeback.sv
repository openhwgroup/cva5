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
        output logic [31:0] rs1_data,
        output logic [31:0] rs2_data,

        //ID Metadata
        output id_t ids_retiring [COMMIT_PORTS],
        output logic retired [COMMIT_PORTS],
        input logic [4:0] retired_rd_addr [COMMIT_PORTS],
        input id_t id_for_rd [COMMIT_PORTS],
        //Writeback
        unit_writeback_interface.wb unit_wb[NUM_WB_UNITS],

        //Trace signals
        output logic tr_rs1_forwarding_needed,
        output logic tr_rs2_forwarding_needed,
        output logic tr_rs1_and_rs2_forwarding_needed
    );

    //Register File
    typedef logic [XLEN-1:0] register_file_t [32];
    register_file_t register_file [COMMIT_PORTS];

    logic [LOG2_COMMIT_PORTS-1:0] rs1_sel;
    logic [LOG2_COMMIT_PORTS-1:0] rs2_sel;

    //Writeback
    logic unit_ack [NUM_WB_UNITS];
    //aliases for write-back-interface signals
    id_t unit_instruction_id [NUM_WB_UNITS];
    logic unit_done [NUM_WB_UNITS];
    logic [XLEN-1:0] unit_rd [NUM_WB_UNITS];
    //Per-ID muxes for commit buffer
    logic [$clog2(NUM_WB_UNITS)-1:0] retiring_unit_select [COMMIT_PORTS];
    logic [31:0] rs1_data_set [COMMIT_PORTS];
    logic [31:0] rs2_data_set [COMMIT_PORTS];

    genvar i;
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
    //Unit select for register file
    //Iterating through all commit ports:
    //   Search for complete units (in fixed unit order)
    //   Assign to a commit port, mask that unit and commit port
    always_comb begin
        unit_ack = '{default: 0};
        retiring_unit_select = '{default: 0};
        retired = '{default: 0};

        for (int i=0; i < COMMIT_PORTS; i++) begin
            for (int j=0; j < NUM_WB_UNITS; j++) begin
                if (unit_done[j] & ~unit_ack[j] & ~retired[i]) begin
                    retiring_unit_select[i] = WB_UNITS_WIDTH'(j);
                    unit_ack[j] = 1;
                    retired[i] = 1;
                end
            end

            //ID muxes
            ids_retiring[i] = unit_instruction_id[retiring_unit_select[i]];
        end
    end

    ////////////////////////////////////////////////////
    //Register Files
    //Implemented in seperate module as there is not universal tool support for inferring
    //arrays of memory blocks.
    generate for (i = 0; i < COMMIT_PORTS; i++) begin
        register_file register_file_blocks (
            .clk, .rst,
            .issue,
            .rd_addr(retired_rd_addr[i]),
            .new_data(unit_rd[retiring_unit_select[i]]),
            .commit(retired[i] & (|retired_rd_addr[i])),
            .rs1_data(rs1_data_set[i]),
            .rs2_data(rs2_data_set[i])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Register File LVT

    //Only update lvt if the retiring instrucion is the most recently issued
    //write to a given register.
    logic update_lvt [COMMIT_PORTS];
    always_comb begin
        for (int i = 0; i < COMMIT_PORTS; i++)
            update_lvt[i] = retired[i];// & (id_for_rd[i] == ids_retiring[i]) OR unit is ALU or other single issue
    end

    regfile_bank_sel regfile_lvt (
        .clk, .rst,
        .rs1_addr(issue.rs1_addr), .rs2_addr(issue.rs2_addr),
        .rs1_sel,
        .rs2_sel,
        .rd_addr(retired_rd_addr),
        .rd_retired(update_lvt)
    );

    ////////////////////////////////////////////////////
    //Register File Muxing
    assign rs1_data = rs1_data_set[rs1_sel];
    assign rs2_data = rs2_data_set[rs2_sel];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
