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

module register_file(
        input logic clk,
        input logic rst,
        input logic gc_supress_writeback,

        input logic instruction_issued,
        register_file_writeback_interface.rf wb,
        register_file_issue_interface.rf issue,

        //Trace signals
        output logic tr_rs1_forwarding_needed,
        output logic tr_rs2_forwarding_needed,
        output logic tr_rs1_and_rs2_forwarding_needed
        );

    (* ramstyle = "MLAB, no_rw_check" *) logic [XLEN-1:0] register [32];
    (* ramstyle = "MLAB, no_rw_check" *) instruction_id_t in_use_by [32];

    logic rs1_inuse;
    logic rs2_inuse;

    logic rs1_feedforward;
    logic rs2_feedforward;

    logic valid_write;
    logic in_use_match;
    //////////////////////////////////////////
    //Assign zero to r0 and initialize all registers to zero
    initial register = '{default: 0};
    initial in_use_by = '{default: 0};

    //Writeback unit does not assert wb.commit when the target register is r0
    always_ff @ (posedge clk) begin
        if (~gc_supress_writeback & valid_write)
            register[wb.rd_addr] <= wb.rd_data;
    end

    assign in_use_match = (wb.id == in_use_by[wb.rd_addr]) && valid_write;

    reg_inuse inuse (.*,
            .clr(1'b0),
            .rs1_addr(issue.rs1_addr),.rs2_addr(issue.rs2_addr), .issued_rd_addr(issue.rd_addr),
            .retired_rd_addr(wb.rd_addr),
            .issued(issue.instruction_issued),
            .retired(in_use_match),
            .rs1_inuse(rs1_inuse),
            .rs2_inuse(rs2_inuse)
            );

    always_ff @ (posedge clk) begin
        if (issue.instruction_issued)
            in_use_by[issue.rd_addr] <= issue.id;
    end

    assign wb.rs1_id = in_use_by[issue.rs1_addr];
    assign wb.rs2_id = in_use_by[issue.rs2_addr];
    assign issue.rs2_id = wb.rs2_id;

    assign valid_write = wb.rd_nzero & wb.retiring;

    assign rs1_feedforward = rs1_inuse;
    assign rs2_feedforward = rs2_inuse;

    assign issue.rs1_data = rs1_feedforward ? wb.rs1_data : register[issue.rs1_addr];
    assign issue.rs2_data = rs2_feedforward ? wb.rs2_data : register[issue.rs2_addr];

    assign issue.rs1_conflict = issue.uses_rs1 & rs1_inuse & ~wb.rs1_valid;
    assign issue.rs2_conflict = issue.uses_rs2 & rs2_inuse & ~wb.rs2_valid;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (!(issue.instruction_issued && issue.rd_addr == 0)) else $error("Write to inuse for register x0 occured!");
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
    generate if (ENABLE_TRACE_INTERFACE) begin
        assign tr_rs1_forwarding_needed = instruction_issued & rs1_inuse & issue.uses_rs1 & ~tr_rs1_and_rs2_forwarding_needed;
        assign tr_rs2_forwarding_needed = instruction_issued & rs2_inuse & issue.uses_rs2 & ~tr_rs1_and_rs2_forwarding_needed;
        assign tr_rs1_and_rs2_forwarding_needed = instruction_issued & (rs1_inuse & issue.uses_rs1) & (rs2_inuse & issue.uses_rs2);
    end
    endgenerate

endmodule
