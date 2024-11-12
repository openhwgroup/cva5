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
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        //ID Management
        input logic pc_id_available,
        input decode_packet_t decode,
        output logic decode_advance,

        //Renamer
        renamer_interface.decode renamer,
        renamer_interface.decode fp_renamer,

        input logic [MAX_NUM_UNITS-1:0] unit_needed,
        input logic [MAX_NUM_UNITS-1:0][REGFILE_READ_PORTS-1:0] unit_uses_rs,
        input logic [1:0][2:0] fp_unit_uses_rs,
        input logic [MAX_NUM_UNITS-1:0] unit_uses_rd,
        input logic [1:0] fp_unit_uses_rd,

        output logic decode_uses_rd,
        output logic fp_decode_uses_rd,
        output rs_addr_t decode_rd_addr,
        output phys_addr_t decode_phys_rd_addr,
        output phys_addr_t fp_decode_phys_rd_addr,
        output phys_addr_t decode_phys_rs_addr [REGFILE_READ_PORTS],
        output phys_addr_t fp_decode_phys_rs_addr [3],
        output logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] decode_rs_wb_group [REGFILE_READ_PORTS],
        output logic fp_decode_rs_wb_group [3],

        output logic instruction_issued,
        output logic instruction_issued_with_rd,
        output logic fp_instruction_issued_with_rd,
        output issue_packet_t issue,
        output rs_addr_t issue_rs_addr [REGFILE_READ_PORTS],
        output phys_addr_t issue_phys_rs_addr [REGFILE_READ_PORTS],
        output phys_addr_t fp_issue_phys_rs_addr [3],
        output logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] issue_rd_wb_group,
        output logic fp_issue_rd_wb_group,
        output logic issue_stage_ready,

        //Register File
        register_file_issue_interface.issue rf,
        register_file_issue_interface.issue fp_rf,

        output logic [31:0] constant_alu,

        unit_issue_interface.decode unit_issue [MAX_NUM_UNITS-1:0],

        input gc_outputs_t gc,
        input logic [1:0] current_privilege,

        exception_interface.unit exception
    );


    common_instruction_t decode_instruction;//rs1_addr, rs2_addr, fn3, fn7, rd_addr, upper/lower opcode

    logic decode_uses_rs [REGFILE_READ_PORTS];
    logic fp_decode_uses_rs [3];

    rs_addr_t decode_rs_addr [REGFILE_READ_PORTS];
    rs_addr_t fp_decode_rs_addr [3];
    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] decode_wb_group;
    logic fp_decode_wb_group;

    logic issue_hold;
    logic [REGFILE_READ_PORTS-1:0] operand_ready;
    logic [2:0] fp_operand_ready;
    logic [MAX_NUM_UNITS-1:0] unit_needed_issue_stage;
    logic [MAX_NUM_UNITS-1:0] issue_to;

    logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] issue_rs_wb_group [REGFILE_READ_PORTS];
    logic fp_issue_rs_wb_group [3];
    logic issue_uses_rs [REGFILE_READ_PORTS];
    logic fp_issue_uses_rs [3];

    logic pre_issue_exception_pending;
    logic illegal_instruction_pattern;
    ////////////////////////////////////////////////////
    //Implementation

    //Can move data into issue stage if:
    // there is no instruction currently in the issue stage, or
    // an instruction could issue (ignoring gc.fetch_flush)
    assign issue_stage_ready = (~issue.stage_valid) | (|issue_to);
    assign decode_advance = decode.valid & issue_stage_ready;

    //Instruction aliases
    assign decode_instruction = decode.instruction;
    always_comb begin
        decode_rs_addr = '{default: '0};
        decode_rs_addr[RS1] = decode_instruction.rs1_addr;
        decode_rs_addr[RS2] = decode_instruction.rs2_addr;
        fp_decode_rs_addr = '{default: '0};
        fp_decode_rs_addr[RS1] = decode_instruction.rs1_addr;
        fp_decode_rs_addr[RS2] = decode_instruction.rs2_addr;
        fp_decode_rs_addr[RS3] = decode_instruction.fn7[6:2];
    end
    ////////////////////////////////////////////////////
    //Register File Support
    always_comb begin
        decode_uses_rd = |unit_uses_rd;
        fp_decode_uses_rd = |fp_unit_uses_rd;
        decode_uses_rs = '{default: 0};
        for (int i = 0; i < MAX_NUM_UNITS; i++)
            for (int j = 0; j < REGFILE_READ_PORTS; j++)
                decode_uses_rs[j] |= unit_uses_rs[i][j];
        fp_decode_uses_rs = '{default: 0};
        for (int i = 0; i < 2; i++)
            for (int j = 0; j < 3; j++)
                fp_decode_uses_rs[j] |= fp_unit_uses_rs[i][j];
    end

    ////////////////////////////////////////////////////
    //WB Group Determination
    localparam units_t [MAX_NUM_UNITS-1:0] WB_UNITS_TYPE_REP = get_wb_units_type_representation(CONFIG.WB_GROUP);
    logic [CONFIG.NUM_WB_GROUPS-1:0] uses_wb_group;
    
    always_comb begin
        for (int i = 0; i < CONFIG.NUM_WB_GROUPS; i++)
            uses_wb_group[i] = |(unit_needed & WB_UNITS_TYPE_REP[i]);
    end

    one_hot_to_integer #(.C_WIDTH(CONFIG.NUM_WB_GROUPS))
    wb_group_one_hot_block (
        .one_hot (uses_wb_group),
        .int_out (decode_wb_group)
    );

    assign fp_decode_wb_group = unit_needed[FPU_ID];

    ////////////////////////////////////////////////////
    //Renamer Support
    assign renamer.rd_addr = decode_instruction.rd_addr;
    assign fp_renamer.rd_addr = decode_instruction.rd_addr;
    assign renamer.rs_addr = decode_rs_addr;
    assign fp_renamer.rs_addr = fp_decode_rs_addr;
    assign renamer.uses_rd = decode_uses_rd;
    assign fp_renamer.uses_rd = fp_decode_uses_rd;
    assign renamer.rd_wb_group = decode_wb_group;
    assign fp_renamer.rd_wb_group = fp_decode_wb_group;
    assign renamer.id = decode.id;
    assign fp_renamer.id = decode.id;

    ////////////////////////////////////////////////////
    //Decode ID Support
    assign decode_rd_addr = decode_instruction.rd_addr;
    assign decode_phys_rd_addr = renamer.phys_rd_addr;
    assign fp_decode_phys_rd_addr = fp_renamer.phys_rd_addr;
    assign decode_phys_rs_addr = renamer.phys_rs_addr;
    assign fp_decode_phys_rs_addr = fp_renamer.phys_rs_addr;
    assign decode_rs_wb_group = renamer.rs_wb_group;
    assign fp_decode_rs_wb_group = fp_renamer.rs_wb_group;

    ////////////////////////////////////////////////////
    //Issue
    always_ff @(posedge clk) begin
        if (instruction_issued) begin
            issue.pc_r <= issue.pc;
            issue.instruction_r <= issue.instruction;
        end
        if (issue_stage_ready) begin
            issue.pc <= decode.pc;
            issue.instruction <= decode.instruction;
            issue.fetch_metadata <= decode.fetch_metadata;
            issue.fn3 <= decode_instruction.fn3;
            issue.opcode <= decode.instruction[6:0];
            issue_rs_addr <= decode_rs_addr;
            issue_phys_rs_addr <= renamer.phys_rs_addr;
            fp_issue_phys_rs_addr <= fp_renamer.phys_rs_addr;
            issue_rs_wb_group <= renamer.rs_wb_group;
            fp_issue_rs_wb_group <= fp_renamer.rs_wb_group;
            issue.rd_addr <= decode_instruction.rd_addr;
            issue.phys_rd_addr <= renamer.phys_rd_addr;
            issue.fp_phys_rd_addr <= fp_renamer.phys_rd_addr;
            issue_rd_wb_group <= decode_wb_group;
            fp_issue_rd_wb_group <= fp_decode_wb_group;
            issue.is_multicycle <= ~unit_needed[ALU_ID];
            issue.id <= decode.id;
            issue_uses_rs <= decode_uses_rs;
            fp_issue_uses_rs <= fp_decode_uses_rs;
            issue.uses_rd <= decode_uses_rd;
            issue.fp_uses_rd <= fp_decode_uses_rd;
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
    //Issue Determination
    assign issue_hold = gc.issue_hold | pre_issue_exception_pending;

    generate for (genvar i=0; i<REGFILE_READ_PORTS; i++)
        assign operand_ready[i] = ~rf.inuse[i] | (rf.inuse[i] & ~issue_uses_rs[i]);
    endgenerate

    generate for (genvar i=0; i<3; i++)
        assign fp_operand_ready[i] = ~fp_rf.inuse[i] | (fp_rf.inuse[i] & ~fp_issue_uses_rs[i]);
    endgenerate

    ////////////////////////////////////////////////////
    //Unit EX signals
    generate for (genvar i = 0; i < MAX_NUM_UNITS; i++) begin : gen_unit_issue_signals
        assign unit_issue[i].possible_issue = issue.stage_valid & unit_needed_issue_stage[i] & unit_issue[i].ready;
        assign issue_to[i] = unit_issue[i].possible_issue & (&operand_ready) & (&fp_operand_ready) & ~issue_hold;
        assign unit_issue[i].new_request = issue_to[i] & ~gc.fetch_flush;
        assign unit_issue[i].id = issue.id;
    end endgenerate

    assign instruction_issued = |issue_to & ~gc.fetch_flush;
    assign instruction_issued_with_rd = instruction_issued & issue.uses_rd;
    assign fp_instruction_issued_with_rd = instruction_issued & issue.fp_uses_rd;

    ////////////////////////////////////////////////////
    //Register File Issue Interface
    assign rf.phys_rs_addr = issue_phys_rs_addr;
    assign fp_rf.phys_rs_addr = fp_issue_phys_rs_addr;
    assign rf.phys_rd_addr = issue.phys_rd_addr;
    assign fp_rf.phys_rd_addr = issue.fp_phys_rd_addr;
    assign rf.rs_wb_group = issue_rs_wb_group;
    assign fp_rf.rs_wb_group = fp_issue_rs_wb_group;
    
    assign rf.single_cycle_or_flush = (instruction_issued_with_rd & |issue.rd_addr & ~issue.is_multicycle) | (issue.stage_valid & issue.uses_rd & |issue.rd_addr & gc.fetch_flush);
    assign fp_rf.single_cycle_or_flush = issue.stage_valid & issue.fp_uses_rd & gc.fetch_flush;
    
    ////////////////////////////////////////////////////
    //Constant ALU:
    //  provides LUI, AUIPC, JAL, JALR results for ALU
    //  provides PC+4 for BRANCH unit and ifence in GC unit
    always_ff @(posedge clk) begin
        if (issue_stage_ready)
            constant_alu <= ((decode_instruction.upper_opcode inside {LUI_T}) ? '0 : decode.pc) + ((decode_instruction.upper_opcode inside {LUI_T, AUIPC_T}) ? {decode.instruction[31:12], 12'b0} : 4); 
    end

    ////////////////////////////////////////////////////
    //Illegal Instruction check
    generate if (CONFIG.MODES != BARE) begin : gen_decode_exceptions
    logic new_exception;
    exception_code_t ecode;
    exception_code_t ecall_code;
    logic [31:0] tval;

    //ECALL and EBREAK captured here, but seperated out when ecode is set
    assign illegal_instruction_pattern = ~|unit_needed;

    ////////////////////////////////////////////////////
    //ECALL/EBREAK
    //The type of call instruction is depedent on the current privilege level
    logic is_ecall;
    logic is_ebreak;
    assign is_ecall = decode.instruction inside {ECALL};
    assign is_ebreak = decode.instruction inside {EBREAK};
    
    always_comb begin
        case (current_privilege)
            USER_PRIVILEGE : ecall_code = ECALL_U;
            SUPERVISOR_PRIVILEGE : ecall_code = ECALL_S;
            MACHINE_PRIVILEGE : ecall_code = ECALL_M;
            default : ecall_code = ECALL_U;
        endcase
    end

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            if (~decode.fetch_metadata.ok)
                ecode <= decode.fetch_metadata.error_code;
            else if (is_ecall)
                ecode <= ecall_code;
            else if (is_ebreak)
                ecode <= BREAK;
            else
                ecode <= ILLEGAL_INST;

            if (~decode.fetch_metadata.ok | is_ebreak)
                tval <= decode.pc;
            else if (is_ecall)
                tval <= '0;
            else
                tval <= decode.instruction;
        end
    end

    ////////////////////////////////////////////////////
    //Exception generation (ecall/ebreak/illegal instruction/propagated fetch error)
    always_ff @(posedge clk) begin
        if (rst)
            pre_issue_exception_pending <= 0;
        else if (issue_stage_ready)
            pre_issue_exception_pending <= illegal_instruction_pattern | (~decode.fetch_metadata.ok);
    end

    assign new_exception = issue.stage_valid & pre_issue_exception_pending & ~(gc.issue_hold | gc.fetch_flush) & ~exception.valid;

    always_ff @(posedge clk) begin
        if (rst)
            exception.valid <= 0;
        else
            exception.valid <= new_exception;
    end

    assign exception.possible = 0; //Not needed because occurs before issue
    assign exception.code = ecode;
    assign exception.tval = tval;
    assign exception.pc = issue.pc;
    assign exception.discard = 0;

    end endgenerate
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
