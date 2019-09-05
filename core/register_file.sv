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

module register_file(
        input logic clk,
        input logic rst,
        input logic inuse_clear,
        input logic gc_supress_writeback,
        register_file_writeback_interface.unit rf_wb,
        register_file_decode_interface.unit rf_decode,

        //Trace signals
        output logic tr_rs1_forwarding_needed,
        output logic tr_rs2_forwarding_needed,
        output logic tr_rs1_and_rs2_forwarding_needed
        );

    (* ramstyle = "MLAB, no_rw_check" *) logic [XLEN-1:0] register [31:0];
    (* ramstyle = "MLAB, no_rw_check" *) instruction_id_t in_use_by [31:0];

    logic rs1_inuse;
    logic rs2_inuse;

    logic rs1_feedforward;
    logic rs2_feedforward;

    logic valid_write;
    logic in_use_match;
    //////////////////////////////////////////
    //Assign zero to r0 and initialize all registers to zero
    initial begin
        for (int i=0; i<32; i++) begin
            register[i] = 0;
            in_use_by[i] = 0;
        end
    end

    //Writeback unit does not assert rf_wb.commit when the target register is r0
    always_ff @ (posedge clk) begin
        if (~gc_supress_writeback & valid_write)
            register[rf_wb.rd_addr] <= rf_wb.rd_data;
    end

    id_inuse inuse_mem (.*,
            .rs1_addr(rf_decode.rs1_addr),.rs2_addr(rf_decode.rs2_addr), .issued_rd_addr(rf_decode.future_rd_addr),
            .issued(rf_decode.instruction_issued),
            .issue_id(rf_decode.id),
            .retired_id(rf_wb.id),
            .retired(valid_write),
            .rs1_inuse(rs1_inuse),
            .rs2_inuse(rs2_inuse)
            );

    always_ff @ (posedge clk) begin
        if (rf_decode.instruction_issued)
            in_use_by[rf_decode.future_rd_addr] <= rf_decode.id;
    end

    assign rf_wb.rs1_id = in_use_by[rf_decode.rs1_addr];
    assign rf_wb.rs2_id = in_use_by[rf_decode.rs2_addr];

    assign valid_write = rf_wb.rd_nzero & rf_wb.retired;

    assign rs1_feedforward = rs1_inuse;
    assign rs2_feedforward = rs2_inuse;

    assign rf_decode.rs1_data = rs1_feedforward ? rf_wb.rs1_data : register[rf_decode.rs1_addr];
    assign rf_decode.rs2_data = rs2_feedforward ? rf_wb.rs2_data : register[rf_decode.rs2_addr];

    assign rf_decode.rs1_conflict = rf_decode.uses_rs1 & rs1_inuse & ~rf_wb.rs1_valid;
    assign rf_decode.rs2_conflict = rf_decode.uses_rs2 & rs2_inuse & ~rf_wb.rs2_valid;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(rf_decode.instruction_issued && rf_decode.future_rd_addr == 0)) else $error("Write to inuse for register x0 occured!");
    end

    ////////////////////////////////////////////////////
    //Simulation Only
    // synthesis translate_off
    logic [31:0][31:0] sim_registers_unamed;
    simulation_named_regfile sim_register;
    always_comb begin
        foreach(register[i])
            sim_registers_unamed[i] = register[i];
        sim_register = sim_registers_unamed;
    end
    // synthesis translate_on

    ////////////////////////////////////////////////////
    //Trace Interface
    assign tr_rs1_forwarding_needed = rs1_inuse & rf_decode.uses_rs1 & ~tr_rs1_and_rs2_forwarding_needed;
    assign tr_rs2_forwarding_needed = rs2_inuse & rf_decode.uses_rs2 & ~tr_rs1_and_rs2_forwarding_needed;
    assign tr_rs1_and_rs2_forwarding_needed = (rs1_inuse & rf_decode.uses_rs1) & (rs2_inuse & rf_decode.uses_rs2);

endmodule
