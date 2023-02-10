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

module decode_and_issue

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import csr_types::*;
    import opcodes::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter NUM_UNITS = 7,
        parameter unit_id_param_t UNIT_IDS = EXAMPLE_UNIT_IDS
    )

    (
        input logic clk,
        input logic rst,

        //ID Management
        input logic pc_id_available,
        input decode_packet_t decode,
        output logic decode_advance,
        output exception_sources_t decode_exception_unit,

        //Renamer
        renamer_interface.decode renamer,

        input logic [NUM_UNITS-1:0] unit_needed,
        input logic [NUM_UNITS-1:0][REGFILE_READ_PORTS-1:0] unit_uses_rs,
        input logic [NUM_UNITS-1:0] unit_uses_rd,

        output logic decode_uses_rd,
        output rs_addr_t decode_rd_addr,
        output phys_addr_t decode_phys_rd_addr,
        output phys_addr_t decode_phys_rs_addr [REGFILE_READ_PORTS],
        output logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] decode_rs_wb_group [REGFILE_READ_PORTS],

        output logic instruction_issued,
        output logic instruction_issued_with_rd,
        output issue_packet_t issue,
        output rs_addr_t issue_rs_addr [REGFILE_READ_PORTS],
        output phys_addr_t issue_phys_rs_addr [REGFILE_READ_PORTS],
        output logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] issue_rd_wb_group,
        output logic issue_stage_ready,

        //Register File
        register_file_issue_interface.issue rf,

        output logic [31:0] constant_alu,

        unit_issue_interface.decode unit_issue [NUM_UNITS-1:0],

        input gc_outputs_t gc,
        input logic [1:0] current_privilege,

        exception_interface.unit exception
    );


    common_instruction_t decode_instruction;//rs1_addr, rs2_addr, fn3, fn7, rd_addr, upper/lower opcode

    logic uses_rs [REGFILE_READ_PORTS];
    logic uses_rd;

    rs_addr_t decode_rs_addr [REGFILE_READ_PORTS];

    logic issue_valid;
    logic operands_ready;

    logic [NUM_UNITS-1:0] unit_needed_issue_stage;
    logic [NUM_UNITS-1:0] unit_ready;
    logic [NUM_UNITS-1:0] issue_ready;
    logic [NUM_UNITS-1:0] issue_to;

    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] issue_rs_wb_group [REGFILE_READ_PORTS];
    logic issue_uses_rs [REGFILE_READ_PORTS];

    logic pre_issue_exception_pending;
    logic illegal_instruction_pattern;
    logic illegal_instruction_pattern_r;

    logic [REGFILE_READ_PORTS-1:0] rs_conflict;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    //Can move data into issue stage if:
    // there is no instruction currently in the issue stage, or
    // an instruction could issue (issue_flush, issue_hold and whether the instruction is valid are not needed in this check)
    assign issue_stage_ready = ((~issue.stage_valid) | (issue_valid & |issue_ready)) & ~gc.issue_hold;
    assign decode_advance = decode.valid & issue_stage_ready;

    //Instruction aliases
    assign decode_instruction = decode.instruction;
    always_comb begin
        decode_rs_addr = '{default: '0};
        decode_rs_addr[RS1] = decode_instruction.rs1_addr;
        decode_rs_addr[RS2] = decode_instruction.rs2_addr;
    end
    ////////////////////////////////////////////////////
    //Register File Support
    always_comb begin
        uses_rd = |unit_uses_rd;
        uses_rs = '{default: 0};
        for (int i = 0; i < NUM_UNITS; i++)
            for (int j = 0; j < REGFILE_READ_PORTS; j++)
                uses_rs[j] |= unit_uses_rs[i][j];
    end

    ////////////////////////////////////////////////////
    //Renamer Support
    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] renamer_wb_group;
    always_comb begin
        renamer_wb_group = $clog2(CONFIG.NUM_WB_GROUPS)'(CONFIG.NUM_WB_GROUPS - 1);
        if (unit_needed[UNIT_IDS.ALU])
            renamer_wb_group = 0;
        else if (unit_needed[UNIT_IDS.LS] )
            renamer_wb_group = 1;
    end
    assign renamer.rd_addr = decode_instruction.rd_addr;
    assign renamer.rs_addr = decode_rs_addr;
    assign renamer.uses_rd = uses_rd;

    assign renamer.rd_wb_group = renamer_wb_group;
    assign renamer.id = decode.id;

    ////////////////////////////////////////////////////
    //Decode ID Support
    assign decode_uses_rd = uses_rd;
    assign decode_rd_addr = decode_instruction.rd_addr;
    assign decode_phys_rd_addr = renamer.phys_rd_addr;
    assign decode_phys_rs_addr = renamer.phys_rs_addr;
    assign decode_rs_wb_group = renamer.rs_wb_group;
    ////////////////////////////////////////////////////
    //Issue
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            issue.pc <= decode.pc;
            issue.instruction <= decode.instruction;
            issue.fetch_metadata <= decode.fetch_metadata;
            issue.fn3 <= decode_instruction.fn3;
            issue.opcode <= decode.instruction[6:0];
            issue_rs_addr <= decode_rs_addr;
            issue_phys_rs_addr <= renamer.phys_rs_addr;
            issue_rs_wb_group <= renamer.rs_wb_group;
            issue.rd_addr <= decode_instruction.rd_addr;
            issue.phys_rd_addr <= renamer.phys_rd_addr;
            issue_rd_wb_group <= renamer_wb_group;
            issue.is_multicycle <= ~unit_needed[UNIT_IDS.ALU];
            issue.id <= decode.id;
            issue.exception_unit <= decode_exception_unit;
            issue_uses_rs <= uses_rs;
            issue.uses_rd <= uses_rd;
        end
    end

    always_ff @(posedge clk) begin
        if (issue_stage_ready)
            unit_needed_issue_stage <= unit_needed;
    end

    always_ff @(posedge clk) begin
        if (rst | gc.fetch_flush)
            issue.stage_valid <= 0;
        else if (issue_stage_ready)
            issue.stage_valid <= decode.valid;
    end

    ////////////////////////////////////////////////////
    //Unit ready
    generate for (i=0; i<NUM_UNITS; i++)
        assign unit_ready[i] = unit_issue[i].ready;
    endgenerate

    ////////////////////////////////////////////////////
    //Issue Determination
    generate for (i=0; i<REGFILE_READ_PORTS; i++)
        assign rs_conflict[i] = rf.inuse[i] & issue_uses_rs[i];
    endgenerate
    assign operands_ready = ~|rs_conflict;

    assign issue_ready = unit_needed_issue_stage & unit_ready;
    assign issue_valid = issue.stage_valid & operands_ready & ~gc.issue_hold & ~pre_issue_exception_pending;

    assign issue_to = {NUM_UNITS{issue_valid & ~gc.fetch_flush}} & issue_ready;

    assign instruction_issued = issue_valid & ~gc.fetch_flush & |issue_ready;
    assign instruction_issued_with_rd = instruction_issued & issue.uses_rd;

    ////////////////////////////////////////////////////
    //Register File Issue Interface
    assign rf.phys_rs_addr = issue_phys_rs_addr;
    assign rf.phys_rd_addr = issue.phys_rd_addr;
    assign rf.rs_wb_group = issue_rs_wb_group;
    
    assign rf.single_cycle_or_flush = (instruction_issued_with_rd & |issue.rd_addr & ~issue.is_multicycle) | (issue.stage_valid & issue.uses_rd & |issue.rd_addr & gc.fetch_flush);
    
    //Constant ALU:
    //  provides LUI, AUIPC, JAL, JALR results for ALU
    //  provides PC+4 for BRANCH unit and ifence in GC unit
    always_ff @(posedge clk) begin
        if (issue_stage_ready)
            constant_alu <= ((decode_instruction.upper_opcode inside {LUI_T}) ? '0 : decode.pc) + ((decode_instruction.upper_opcode inside {LUI_T, AUIPC_T}) ? {decode.instruction[31:12], 12'b0} : 4); 
    end

    ////////////////////////////////////////////////////
    //Unit EX signals
    generate for (i = 0; i < NUM_UNITS; i++) begin : gen_unit_issue_signals
        assign unit_issue[i].possible_issue = issue.stage_valid & unit_needed_issue_stage[i] & unit_issue[i].ready;
        assign unit_issue[i].new_request = issue_to[i];
        assign unit_issue[i].id = issue.id;
    end endgenerate

    ////////////////////////////////////////////////////
    //Illegal Instruction check
    generate if (CONFIG.INCLUDE_M_MODE) begin : gen_decode_exceptions

    assign illegal_instruction_pattern = ~|unit_needed;
    always_ff @(posedge clk) begin
        if (rst)
            illegal_instruction_pattern_r <= 0;
        else if (issue_stage_ready)
            illegal_instruction_pattern_r <= illegal_instruction_pattern;
    end

    //TODO: Consider ways of parameterizing so that any exception generating unit
    //can be automatically added to this expression
    always_comb begin
        unique case (1'b1)
            unit_needed[UNIT_IDS.LS] : decode_exception_unit = LS_EXCEPTION;
            unit_needed[UNIT_IDS.BR] : decode_exception_unit = BR_EXCEPTION;
            default : decode_exception_unit = PRE_ISSUE_EXCEPTION;
        endcase
        if (illegal_instruction_pattern)
            decode_exception_unit = PRE_ISSUE_EXCEPTION;
    end

    ////////////////////////////////////////////////////
    //ECALL/EBREAK
    //The type of call instruction is depedent on the current privilege level
    exception_code_t ecall_code;
    always_comb begin
        case (current_privilege)
            USER_PRIVILEGE : ecall_code = ECALL_U;
            SUPERVISOR_PRIVILEGE : ecall_code = ECALL_S;
            MACHINE_PRIVILEGE : ecall_code = ECALL_M;
            default : ecall_code = ECALL_U;
        endcase
    end

    ////////////////////////////////////////////////////
    //Exception generation (ecall/ebreak/illegal instruction/propagated fetch error)
    logic new_exception;
    exception_code_t ecode;

    always_ff @(posedge clk) begin
        if (rst)
            pre_issue_exception_pending <= 0;
        else if (issue_stage_ready)
            pre_issue_exception_pending <= illegal_instruction_pattern | (~decode.fetch_metadata.ok) | decode.instruction inside {ECALL, EBREAK};
    end

    assign new_exception = issue.stage_valid & pre_issue_exception_pending & ~(gc.issue_hold | gc.fetch_flush);

    always_ff @(posedge clk) begin
        if (rst)
            exception.valid <= 0;
        else
            exception.valid <= (exception.valid | new_exception) & ~exception.ack;
    end

    logic is_ecall_r;
    always_ff @(posedge clk) begin
        if (issue_stage_ready)
            is_ecall_r <= (decode_instruction.upper_opcode == SYSTEM_T) & (decode.instruction[31:20] == ECALL_imm);
    end

    assign ecode =
        illegal_instruction_pattern_r ? ILLEGAL_INST :
        is_ecall_r ? ecall_code :
        ~issue.fetch_metadata.ok ? issue.fetch_metadata.error_code :
        BREAK;

    always_ff @(posedge clk) begin
        if (new_exception) begin
            exception.code <= ecode;
            exception.tval <= issue.instruction;
            exception.id <= issue.id;
        end
    end

    end endgenerate
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
