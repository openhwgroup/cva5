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

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import csr_types::*;
    import fpu_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter NUM_UNITS = 7,
        parameter unit_id_param_t UNIT_IDS = EXAMPLE_UNIT_IDS,
        parameter FP_NUM_UNITS = 4,
        parameter fp_unit_id_param_t FP_UNIT_IDS = FP_EXAMPLE_UNIT_IDS,
        parameter TOTAL_NUM_UNITS = NUM_UNITS + FP_NUM_UNITS
    )

    (
        input logic clk,
        input logic rst,

        //ID Management
        input logic pc_id_available,
        input logic [LOG2_MAX_IDS:0] post_issue_count,
        input decode_packet_t decode,
        output logic decode_advance,
        output exception_sources_t decode_exception_unit,

        //Renamer
        renamer_interface.decode renamer,
        fp_renamer_interface.decode fp_renamer,

        output logic decode_uses_rd,
        output rs_addr_t decode_rd_addr,
        output phys_addr_t decode_phys_rd_addr,
        output phys_addr_t decode_phys_rs_addr [REGFILE_READ_PORTS],
        output logic [$clog2(CONFIG.NUM_WB_GROUPS)-1:0] decode_rs_wb_group [REGFILE_READ_PORTS],

        output logic fp_decode_uses_rd,
        output phys_addr_t fp_decode_phys_rd_addr,
        output phys_addr_t fp_decode_phys_rs_addr [FP_REGFILE_READ_PORTS],
        //output logic [$clog2(CONFIG.FP.FP_NUM_WB_GROUPS)-1:0] fp_decode_rs_wb_group [FP_REGFILE_READ_PORTS],
        output logic fp_decode_rs_wb_group [FP_REGFILE_READ_PORTS],

        output logic instruction_issued,
        output logic instruction_issued_with_rd,
        output logic fp_instruction_issued_with_rd,
        output issue_packet_t issue,

        //Register File
        register_file_issue_interface.issue rf,
        fp_register_file_issue_interface.issue fp_rf,
        input logic [2:0] dyn_rm,

        output alu_inputs_t alu_inputs,
        output load_store_inputs_t ls_inputs,
        output branch_inputs_t branch_inputs,
        output gc_inputs_t gc_inputs,
        output csr_inputs_t csr_inputs,
        output mul_inputs_t mul_inputs,
        output div_inputs_t div_inputs,
        output fp_madd_inputs_t fp_madd_inputs,
        output fp_cmp_inputs_t fp_cmp_inputs,
        output fp_div_sqrt_inputs_t fp_div_sqrt_inputs,
        output fp_cvt_mv_inputs_t fp_cvt_mv_inputs,

        unit_issue_interface.decode unit_issue [TOTAL_NUM_UNITS-1:0],

        input gc_outputs_t gc,
        input logic [1:0] current_privilege,

        exception_interface.unit exception,

        //Trace signals
        output logic tr_operand_stall,
        output logic tr_unit_stall,
        output logic tr_no_id_stall,
        output logic tr_no_instruction_stall,
        output logic tr_other_stall,
        output logic tr_branch_operand_stall,
        output logic tr_alu_operand_stall,
        output logic tr_ls_operand_stall,
        output logic tr_div_operand_stall,

        output logic tr_alu_op,
        output logic tr_branch_or_jump_op,
        output logic tr_load_op,
        output logic tr_store_op,
        output logic tr_mul_op,
        output logic tr_div_op,
        output logic tr_misc_op,

        output logic tr_instruction_issued_dec,
        output logic [31:0] tr_instruction_pc_dec,
        output logic [31:0] tr_instruction_data_dec
        );

    logic [2:0] fn3;
    logic [6:0] opcode;
    logic [6:0] fn7;
    logic [4:0] opcode_trim;

    logic uses_rs1;
    logic uses_rs2;
    logic uses_rd;

    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] rs3_addr;
    logic [4:0] rd_addr;

    logic is_csr;
    logic is_fence;
    logic is_ifence;
    logic csr_imm_op;
    logic environment_op;
    logic is_i2f;
    logic is_f2i;
    logic is_class;
    logic is_fcmp;     

    logic issue_valid;
    logic operands_ready;
    logic fp_operands_ready;
    logic mult_div_op;

    logic [TOTAL_NUM_UNITS-1:0] unit_needed;
    logic [TOTAL_NUM_UNITS-1:0] unit_needed_issue_stage;
    logic [TOTAL_NUM_UNITS-1:0] unit_ready;
    logic [TOTAL_NUM_UNITS-1:0] issue_ready;
    logic [TOTAL_NUM_UNITS-1:0] issue_to;

    logic pre_issue_exception_pending;
    logic illegal_instruction_pattern;

    logic issue_stage_ready;

    logic rs1_conflict;
    logic rs2_conflict;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation
    
    //Can move data into issue stage if:
    // there is no instruction currently in the issue stage, or
    // an instruction could issue (issue_flush, issue_hold and whether the instruction is valid are not needed in this check)
    assign issue_stage_ready = (~issue.stage_valid) | (issue_valid & |issue_ready);
    assign decode_advance = decode.valid & issue_stage_ready;

    //Instruction aliases
    assign opcode = decode.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn7 = decode.instruction[31:25];
    assign fn3 = decode.instruction[14:12];
    assign rs1_addr = decode.instruction[19:15];
    assign rs2_addr = decode.instruction[24:20];
    assign rs3_addr = decode.instruction[31:27];
    assign rd_addr = decode.instruction[11:7];

    assign is_csr = (opcode_trim == SYSTEM_T) & (fn3 != 0);
    assign is_fence = (opcode_trim == FENCE_T) & ~fn3[0];
    assign is_ifence = (opcode_trim == FENCE_T) & fn3[0];
    assign csr_imm_op = (opcode_trim == SYSTEM_T) & fn3[2];
    assign environment_op = (opcode_trim == SYSTEM_T) & (fn3 == 0);

    ////////////////////////////////////////////////////
    //Register File Support
    assign uses_rs1 = opcode_trim inside {JALR_T, BRANCH_T, LOAD_T, STORE_T, ARITH_IMM_T, ARITH_T, AMO_T} | is_csr | is_i2f;
    assign uses_rs2 = opcode_trim inside {BRANCH_T, ARITH_T, AMO_T};//Stores are exempted due to store forwarding
    assign uses_rd = opcode_trim inside {LUI_T, AUIPC_T, JAL_T, JALR_T, LOAD_T, ARITH_IMM_T, ARITH_T} | is_csr | is_f2i | is_fcmp | is_class; 
    //assign uses_rs1 = !(opcode_trim inside {LUI_T, AUIPC_T, JAL_T, FENCE_T, FMADD_T, FMSUB_T, FNMADD_T, FNMSUB_T} || csr_imm_op || environment_op || (opcode_trim == FOP_T && fn7 != FCVT_DW));
    //assign uses_rs2 = opcode_trim inside {BRANCH_T, ARITH_T, AMO_T};//Stores are exempted due to store forwarding
    //assign uses_rd = (!(opcode_trim inside {BRANCH_T, STORE_T, FENCE_T, FSD_T} || environment_op) || is_f2i || is_class || is_fcmp) & ~decode.wb2_float;

    ////////////////////////////////////////////////////
    //Unit Determination
    assign unit_needed[UNIT_IDS.BR] = opcode_trim inside {BRANCH_T, JAL_T, JALR_T};
    assign unit_needed[UNIT_IDS.ALU] = (opcode_trim inside {ARITH_T, ARITH_IMM_T, AUIPC_T, LUI_T, JAL_T, JALR_T}) & ~mult_div_op;
    assign unit_needed[UNIT_IDS.LS] = opcode_trim inside {LOAD_T, STORE_T, AMO_T, FLD_T, FSD_T};
    assign unit_needed[UNIT_IDS.CSR] = is_csr;
    assign unit_needed[UNIT_IDS.IEC] = (opcode_trim inside {SYSTEM_T} & ~is_csr) | is_ifence;

    assign mult_div_op = (opcode_trim == ARITH_T) && decode.instruction[25];
    generate if (CONFIG.INCLUDE_MUL)
        assign unit_needed[UNIT_IDS.MUL] = mult_div_op && ~fn3[2];
    endgenerate

    generate if (CONFIG.INCLUDE_DIV)
        assign unit_needed[UNIT_IDS.DIV] = mult_div_op && fn3[2];
    endgenerate

    ////////////////////////////////////////////////////
    //Renamer Support
    assign renamer.rd_addr = rd_addr;
    assign renamer.rs_addr[RS1] = rs1_addr;
    assign renamer.rs_addr[RS2] = rs2_addr;
    assign renamer.uses_rd = uses_rd;
    assign renamer.rd_wb_group = ~unit_needed[UNIT_IDS.ALU];//TODO: automate generation of wb group logic
    assign renamer.id = decode.id;
    
    ////////////////////////////////////////////////////
    //Decode ID Support
    assign decode_uses_rd = uses_rd;
    assign decode_rd_addr = rd_addr;
    assign decode_phys_rd_addr = renamer.phys_rd_addr;
    assign decode_phys_rs_addr[RS1] = renamer.phys_rs_addr[RS1];
    assign decode_phys_rs_addr[RS2] = renamer.phys_rs_addr[RS2];
    assign decode_rs_wb_group[RS1] = renamer.rs_wb_group[RS1];
    assign decode_rs_wb_group[RS2] = renamer.rs_wb_group[RS2];

    //TODO: Consider ways of parameterizing so that any exception generating unit
    //can be automatically added to this expression
    //TODO: Does FPU need to be added here?
    exception_sources_t decode_exception_unit;
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
    //Issue
    logic [REGFILE_READ_PORTS-1:0][$clog2(CONFIG.NUM_WB_GROUPS)-1:0] issue_rs_wb_group;

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            issue.pc <= decode.pc;
            issue.instruction <= decode.instruction;
            issue.fetch_metadata <= decode.fetch_metadata;
            issue.fn3 <= fn3;
            issue.opcode <= opcode;
            issue.rs_addr[RS1] <= rs1_addr;
            issue.rs_addr[RS2] <= rs2_addr;
            issue.phys_rs_addr[RS1] <= renamer.phys_rs_addr[RS1];
            issue.phys_rs_addr[RS2] <= renamer.phys_rs_addr[RS2];
            issue_rs_wb_group <= renamer.rs_wb_group;
            issue.rd_addr <= rd_addr;
            issue.phys_rd_addr <= renamer.phys_rd_addr;
            issue.is_multicycle <= ~unit_needed[UNIT_IDS.ALU];
            issue.id <= decode.id;
            issue.exception_unit <= decode_exception_unit;
            issue.uses_rs1 <= uses_rs1;
            issue.uses_rs2 <= uses_rs2;
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
    generate for (i=0; i<TOTAL_NUM_UNITS; i++) begin
        assign unit_ready[i] = unit_issue[i].ready;
    end endgenerate

    ////////////////////////////////////////////////////
    //Issue Determination
    assign rs1_conflict = rf.inuse[RS1] & issue.uses_rs1;
    assign rs2_conflict = rf.inuse[RS2] & issue.uses_rs2;
    assign operands_ready = (~rs1_conflict) & (~rs2_conflict);

    assign issue_ready = unit_needed_issue_stage & unit_ready;
    //TODO: may need to fix operand_ready logic to avoid waiting for unneeded register conflicts
    assign issue_valid = issue.stage_valid & operands_ready & fp_operands_ready & ~gc.issue_hold & ~pre_issue_exception_pending;

    assign issue_to = {TOTAL_NUM_UNITS{issue_valid & ~gc.fetch_flush}} & issue_ready;

    assign instruction_issued = issue_valid & ~gc.fetch_flush & |issue_ready;
    assign instruction_issued_with_rd = instruction_issued & ~issue.wb2_float & issue.uses_rd;

    assign rf.phys_rs_addr[RS1] = issue.phys_rs_addr[RS1];
    assign rf.phys_rs_addr[RS2] = issue.phys_rs_addr[RS2];
    assign rf.phys_rd_addr = issue.phys_rd_addr;
    assign rf.rs_wb_group[RS1] = issue_rs_wb_group[RS1];
    assign rf.rs_wb_group[RS2] = issue_rs_wb_group[RS2];
    assign rf.single_cycle_or_flush = (instruction_issued_with_rd & |issue.rd_addr & ~issue.is_multicycle) | (issue.stage_valid & issue.uses_rd & |issue.rd_addr & gc.fetch_flush);
    
    ////////////////////////////////////////////////////
    //ALU unit inputs
    logic [XLEN-1:0] alu_rs2_data;
    logic alu_imm_type;
    logic [31:0] constant_alu;
    alu_op_t alu_op;
    alu_op_t alu_op_r;
    alu_logic_op_t alu_logic_op;
    alu_logic_op_t alu_logic_op_r;
    logic alu_subtract;
    logic sub_instruction;

    always_comb begin
        case (opcode_trim) inside
            LUI_T, AUIPC_T, JAL_T, JALR_T : alu_op = ALU_CONSTANT;
            default : 
            case (fn3) inside
                SLTU_fn3, SLT_fn3 : alu_op = ALU_SLT;
                SLL_fn3, SRA_fn3 : alu_op = ALU_SHIFT;
                default : alu_op = ALU_ADD_SUB;
            endcase
        endcase
    end

    always_comb begin
        case (fn3)
            XOR_fn3 : alu_logic_op = ALU_LOGIC_XOR;
            OR_fn3 : alu_logic_op = ALU_LOGIC_OR;
            AND_fn3 : alu_logic_op = ALU_LOGIC_AND;
            default : alu_logic_op = ALU_LOGIC_ADD;//ADD/SUB/SLT/SLTU
        endcase
    end

    assign sub_instruction = (fn3 == ADD_SUB_fn3) && decode.instruction[30] && opcode[5];//If ARITH instruction

    //Constant ALU:
    //  provides LUI, AUIPC, JAL, JALR results for ALU
    //  provides PC+4 for BRANCH unit
    // TODO: ifence in GC unit, others?
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            constant_alu <= ((opcode_trim inside {LUI_T}) ? '0 : decode.pc) + ((opcode_trim inside {LUI_T, AUIPC_T}) ? {decode.instruction[31:12], 12'b0} : 4); 
            alu_imm_type <= opcode_trim inside {ARITH_IMM_T};
            alu_op_r <= alu_op;
            alu_subtract <= (fn3 inside {SLTU_fn3, SLT_fn3}) || sub_instruction;
            alu_logic_op_r <= alu_logic_op;
        end
    end

    //Shifter related
    assign alu_inputs.lshift = ~issue.fn3[2];
    assign alu_inputs.shift_amount = alu_imm_type ? issue.rs_addr[RS2] : rf.data[RS2][4:0];
    assign alu_inputs.arith = rf.data[RS1][XLEN-1] & issue.instruction[30];//shift in bit
    assign alu_inputs.shifter_in = rf.data[RS1];

    //LUI, AUIPC, JAL, JALR
    assign alu_inputs.constant_adder = constant_alu;

    //logic and adder
    assign alu_inputs.subtract = alu_subtract;
    assign alu_inputs.logic_op = alu_logic_op_r;
    assign alu_inputs.in1 = {(rf.data[RS1][XLEN-1] & ~issue.fn3[0]), rf.data[RS1]};//(fn3[0]  is SLTU_fn3);
    assign alu_rs2_data = alu_imm_type ? 32'(signed'(issue.instruction[31:20])) : rf.data[RS2];
    assign alu_inputs.in2 = {(alu_rs2_data[XLEN-1] & ~issue.fn3[0]), alu_rs2_data};

    assign alu_inputs.alu_op = alu_op_r;
    ////////////////////////////////////////////////////
    //Load Store unit inputs
    logic is_load;
    logic is_store;
    logic amo_op;
    logic store_conditional;
    logic load_reserve;
    logic [4:0] amo_type;

    assign amo_op =  CONFIG.INCLUDE_AMO ? (opcode_trim == AMO_T) : 1'b0;
    assign amo_type = decode.instruction[31:27];
    assign store_conditional = (amo_type == AMO_SC_FN5);
    assign load_reserve = (amo_type == AMO_LR_FN5);

    generate if (CONFIG.INCLUDE_AMO) begin
            assign ls_inputs.amo.is_lr = load_reserve;
            assign ls_inputs.amo.is_sc = store_conditional;
            assign ls_inputs.amo.is_amo = amo_op & ~(load_reserve | store_conditional);
            assign ls_inputs.amo.op = amo_type;
        end
        else begin
            assign ls_inputs.amo = '0;
        end
    endgenerate

    assign is_load = (opcode_trim inside {LOAD_T, FLD_T, AMO_T}) && !(amo_op & store_conditional); //LR and AMO_ops perform a read operation as well
    assign is_store = (opcode_trim inside {STORE_T, FSD_T}) || (amo_op && store_conditional);//Used for LS unit and for ID tracking

    logic [11:0] ls_offset;
    logic is_load_r;
    logic is_store_r;
    logic is_fence_r;
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            ls_offset <= opcode[5] ? {decode.instruction[31:25], decode.instruction[11:7]} : decode.instruction[31:20];
            is_load_r <= is_load;
            is_store_r <= is_store;
            is_fence_r <= is_fence;
        end
    end

    (* ramstyle = "MLAB, no_rw_check" *) id_t rd_to_id_table [32];
    always_ff @ (posedge clk) begin
        if (instruction_issued_with_rd | fp_instruction_issued_with_rd)
            rd_to_id_table[issue.rd_addr] <= issue.id;
    end

    assign ls_inputs.offset = ls_offset;
    assign ls_inputs.load = is_load_r;
    assign ls_inputs.store = is_store_r;
    assign ls_inputs.fence = is_fence_r;
    assign ls_inputs.fn3 = amo_op ? LS_W_fn3 : issue.fn3;
    assign ls_inputs.rs1 = rf.data[RS1];
    assign ls_inputs.rs2 = rf.data[RS2];
    assign ls_inputs.forwarded_store = rf.inuse[RS2];
    assign ls_inputs.store_forward_id = rd_to_id_table[issue.rs_addr[RS2]];

    //FPU support
    assign ls_inputs.is_float = issue.is_float;
    assign ls_inputs.fp_rs2 = fp_rf.data[RS2];
    assign ls_inputs.fp_forwarded_store = fp_rf.inuse[RS2];

    ls_input_assertion:
        assert property (@(posedge clk) disable iff (rst) instruction_issued  & issue_to[UNIT_IDS.LS] &ls_inputs.store|-> !(issue.fp_uses_rd | issue.uses_rd))
        else $error("store issued with uses_rd");

    ////////////////////////////////////////////////////
    //Branch unit inputs

    ////////////////////////////////////////////////////
    //RAS Support
    logic rs1_link;
    logic rd_link;
    logic rs1_eq_rd;
    logic is_return;
    logic is_call;
    assign rs1_link = (rs1_addr inside {1,5});
    assign rd_link = (rd_addr inside {1,5});
    assign rs1_eq_rd = (rs1_addr == rd_addr);

    logic br_use_signed;

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            is_return <= (opcode_trim == JALR_T) && ((rs1_link & ~rd_link) | (rs1_link & rd_link & ~rs1_eq_rd));
            is_call <= (opcode_trim inside {JAL_T, JALR_T}) && rd_link;
            br_use_signed <= !(fn3 inside {BLTU_fn3, BGEU_fn3});
        end
    end

    logic[19:0] jal_imm;
    logic[11:0] jalr_imm;
    logic[11:0] br_imm;

    logic [20:0] pc_offset;
    logic [20:0] pc_offset_r;
    assign jal_imm = {decode.instruction[31], decode.instruction[19:12], decode.instruction[20], decode.instruction[30:21]};
    assign jalr_imm = decode.instruction[31:20];
    assign br_imm = {decode.instruction[31], decode.instruction[7], decode.instruction[30:25], decode.instruction[11:8]};


    always_comb begin
        case (opcode[3:2])
            2'b11 : pc_offset = 21'(signed'({jal_imm, 1'b0}));
            2'b01 : pc_offset = 21'(signed'(jalr_imm));
            default : pc_offset = 21'(signed'({br_imm, 1'b0}));
        endcase
    end

    logic jalr;
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            pc_offset_r <= pc_offset;
            jalr <= (~opcode[3] & opcode[2]);
        end
    end

    logic[2:0] br_fn3;

    assign branch_inputs.is_return = is_return;
    assign branch_inputs.is_call = is_call;
    assign branch_inputs.fn3 = issue.fn3;
    assign branch_inputs.pc_offset = pc_offset_r;
    assign branch_inputs.jal = issue.opcode[3];//(opcode == JAL);
    assign branch_inputs.jalr = jalr;
    assign branch_inputs.jal_jalr = issue.opcode[2];

    assign branch_inputs.issue_pc = issue.pc;
    assign branch_inputs.issue_pc_valid = issue.stage_valid;
    assign branch_inputs.rs1 = {(rf.data[RS1][31] & br_use_signed), rf.data[RS1]};
    assign branch_inputs.rs2 = {(rf.data[RS2][31] & br_use_signed), rf.data[RS2]};
    assign branch_inputs.pc_p4 = constant_alu;

    ////////////////////////////////////////////////////
    //Global Control unit inputs
    logic is_ecall_r;
    logic is_ebreak_r;
    logic is_mret_r;
    logic is_sret_r;
    logic is_ifence_r;

    logic [7:0] sys_op_match;
    typedef enum logic [2:0] {
        ECALL_i = 0,
        EBREAK_i = 1,
        URET_i = 2,
        SRET_i = 3,
        MRET_i = 4,
        SFENCE_i = 5
    } sys_op_index_t;

    always_comb begin
        sys_op_match = '0;
        case (decode.instruction[31:20]) inside
            ECALL_imm : sys_op_match[ECALL_i] = CONFIG.INCLUDE_M_MODE;
            EBREAK_imm : sys_op_match[EBREAK_i] = CONFIG.INCLUDE_M_MODE;
            SRET_imm : sys_op_match[SRET_i] = CONFIG.INCLUDE_S_MODE;
            MRET_imm : sys_op_match[MRET_i] = CONFIG.INCLUDE_M_MODE;
            SFENCE_imm : sys_op_match[SFENCE_i] = CONFIG.INCLUDE_S_MODE;
            default : sys_op_match = '0;
        endcase
    end

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            is_ecall_r <= sys_op_match[ECALL_i];
            is_ebreak_r <= sys_op_match[EBREAK_i];
            is_mret_r <= sys_op_match[MRET_i];
            is_sret_r <= sys_op_match[SRET_i];
            is_ifence_r <= is_ifence;
        end
    end

    assign gc_inputs.pc_p4 = constant_alu;
    assign gc_inputs.is_ifence = is_ifence_r;
    assign gc_inputs.is_mret = is_mret_r;
    assign gc_inputs.is_mret = is_sret_r;

    ////////////////////////////////////////////////////
    //CSR unit inputs
    assign csr_inputs.addr = issue.instruction[31:20];
    assign csr_inputs.op = issue.fn3[1:0];
    assign csr_inputs.data = issue.fn3[2] ? {27'b0, issue.rs_addr[RS1]} : rf.data[RS1];
    assign csr_inputs.reads = ~((issue.fn3[1:0] == CSR_RW) && (issue.rd_addr == 0));
    assign csr_inputs.writes = ~((issue.fn3[1:0] == CSR_RC) && (issue.rs_addr[RS1] == 0));

    ////////////////////////////////////////////////////
    //Mul unit inputs
    generate if (CONFIG.INCLUDE_MUL) begin
        assign mul_inputs.rs1 = rf.data[RS1];
        assign mul_inputs.rs2 = rf.data[RS2];
        assign mul_inputs.op = issue.fn3[1:0];
    end endgenerate

    ////////////////////////////////////////////////////
    //Div unit inputs
    generate if (CONFIG.INCLUDE_DIV) begin
        logic [4:0] prev_div_rs1_addr;
        logic [4:0] prev_div_rs2_addr;
        logic prev_div_result_valid;
        logic div_rs_overwrite;
        logic div_op_reuse;

        always_ff @(posedge clk) begin
            if (issue_to[UNIT_IDS.DIV]) begin
                prev_div_rs1_addr <= rs1_addr;
                prev_div_rs2_addr <= rs2_addr;
            end
        end

        assign div_op_reuse = {prev_div_result_valid, prev_div_rs1_addr, prev_div_rs2_addr} == {1'b1, issue.rs_addr[RS1], issue.rs_addr[RS2]};

        //If current div operation overwrites an input register OR any other instruction overwrites the last div operations input registers
        assign div_rs_overwrite = (issue.rd_addr == (unit_needed_issue_stage[UNIT_IDS.DIV] ? issue.rs_addr[RS1] : prev_div_rs1_addr)) || (issue.rd_addr == (unit_needed_issue_stage[UNIT_IDS.DIV] ? issue.rs_addr[RS2] : prev_div_rs2_addr));

        set_clr_reg_with_rst #(.SET_OVER_CLR(0), .WIDTH(1), .RST_VALUE(0)) prev_div_result_valid_m (
            .clk, .rst,
            .set(instruction_issued & unit_needed_issue_stage[UNIT_IDS.DIV]),
            .clr(instruction_issued & issue.uses_rd & div_rs_overwrite),
            .result(prev_div_result_valid)
        );

        assign div_inputs.rs1 = rf.data[RS1];
        assign div_inputs.rs2 = rf.data[RS2];
        assign div_inputs.op = issue.fn3[1:0];
        assign div_inputs.reuse_result = div_op_reuse;
    end endgenerate

    ////////////////////////////////////////////////////
    //Unit EX signals
    generate for (i = 0; i < TOTAL_NUM_UNITS; i++) begin
        assign unit_issue[i].possible_issue = issue.stage_valid & unit_needed_issue_stage[i] & unit_issue[i].ready;
        assign unit_issue[i].new_request = issue_to[i];
        assign unit_issue[i].id = issue.id;
        always_ff @(posedge clk) begin
            unit_issue[i].new_request_r <= issue_to[i];
        end
    end endgenerate

    ////////////////////////////////////////////////////
    //FPU support
    generate if (CONFIG.FP.INCLUDE_FPU) begin
        fp_decode_and_issue #(
            .CONFIG(CONFIG),
            .FP_NUM_UNITS(FP_NUM_UNITS),
            .FP_UNIT_IDS(FP_UNIT_IDS)
            )
        fp_decode_and_issue_block (
            .clk (clk),
            .rst (rst),
            .decode (decode),
            .fp_renamer (fp_renamer),
            .fp_decode_uses_rd (fp_decode_uses_rd),
            .fp_decode_phys_rd_addr (fp_decode_phys_rd_addr),
            .fp_decode_phys_rs_addr (fp_decode_phys_rs_addr),
            .fp_decode_rs_wb_group (fp_decode_rs_wb_group),
            .unit_needed (unit_needed[TOTAL_NUM_UNITS-1-:FP_NUM_UNITS]),
            .is_i2f (is_i2f),
            .is_f2i (is_f2i),
            .is_class (is_class),
            .is_fcmp (is_fcmp),
            .issue (issue),
            .issue_stage_ready (issue_stage_ready),
            .instruction_issued (instruction_issued),
            .fp_instruction_issued_with_rd (fp_instruction_issued_with_rd),
            .int_rs1_data (rf.data[RS1]),
            .fp_rf (fp_rf),
            .dyn_rm (dyn_rm),
            .fp_operands_ready (fp_operands_ready),
            .fp_madd_inputs (fp_madd_inputs),
            .fp_cmp_inputs (fp_cmp_inputs),
            .fp_div_sqrt_inputs (fp_div_sqrt_inputs),
            .fp_cvt_mv_inputs (fp_cvt_mv_inputs),
            .gc_fetch_flush (gc.fetch_flush)
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Illegal Instruction check
    logic illegal_instruction_pattern_r;
    generate if (CONFIG.INCLUDE_M_MODE) begin
    illegal_instruction_checker # (.CONFIG(CONFIG))
    illegal_op_check (
        .instruction(decode.instruction), .illegal_instruction(illegal_instruction_pattern)
    );
    always_ff @(posedge clk) begin
        if (rst)
            illegal_instruction_pattern_r <= 0;
        else if (issue_stage_ready)
            illegal_instruction_pattern_r <= illegal_instruction_pattern;
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
            pre_issue_exception_pending <= illegal_instruction_pattern | (opcode_trim inside {SYSTEM_T} & ~is_csr & (sys_op_match[ECALL_i] | sys_op_match[EBREAK_i])) | ~decode.fetch_metadata.ok;
    end

    assign new_exception = issue.stage_valid & pre_issue_exception_pending & ~(gc.issue_hold | gc.fetch_flush);

    always_ff @(posedge clk) begin
        if (rst)
            exception.valid <= 0;
        else
            exception.valid <= (exception.valid | new_exception) & ~exception.ack;
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

    instruction_issued_with_rd_assertion:
        assert property (@(posedge clk) disable iff (rst) instruction_issued |-> ~(instruction_issued_with_rd & fp_instruction_issued_with_rd))
        else $error("both instruction_issued_with_rd set");

    decode_uses_rd_assertion:
        assert property (@(posedge clk) disable iff (rst) decode_advance |-> ~(decode_uses_rd & fp_decode_uses_rd))
        else $error("both decode uses rd are asserted");

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin
        assign tr_operand_stall = issue.stage_valid & ~gc.fetch_flush & ~gc.issue_hold & ~operands_ready & |issue_ready;
        assign tr_unit_stall = issue_valid & ~gc.fetch_flush & ~|issue_ready;
        assign tr_no_id_stall = (~issue.stage_valid & ~pc_id_available & ~gc.fetch_flush); //All instructions in execution pipeline
        assign tr_no_instruction_stall = (~tr_no_id_stall & ~issue.stage_valid) | gc.fetch_flush;
        assign tr_other_stall = issue.stage_valid & ~instruction_issued & ~(tr_operand_stall | tr_unit_stall | tr_no_id_stall | tr_no_instruction_stall);
        assign tr_branch_operand_stall = tr_operand_stall & unit_needed_issue_stage[UNIT_IDS.BR];
        assign tr_alu_operand_stall = tr_operand_stall & unit_needed_issue_stage[UNIT_IDS.ALU] & ~unit_needed_issue_stage[UNIT_IDS.BR];
        assign tr_ls_operand_stall = tr_operand_stall & unit_needed_issue_stage[UNIT_IDS.LS];
        assign tr_div_operand_stall = tr_operand_stall & unit_needed_issue_stage[UNIT_IDS.DIV];

        //Instruction Mix
        always_ff @(posedge clk) begin
            if (issue_stage_ready) begin
                tr_alu_op <= instruction_issued && (opcode_trim inside {ARITH_T, ARITH_IMM_T, AUIPC_T, LUI_T} && ~tr_mul_op && ~tr_div_op);
                tr_branch_or_jump_op <= instruction_issued && (opcode_trim inside {JAL_T, JALR_T, BRANCH_T});
                tr_load_op <= instruction_issued && (opcode_trim inside {LOAD_T, AMO_T});
                tr_store_op <= instruction_issued && (opcode_trim inside {STORE_T});
                tr_mul_op <= instruction_issued && unit_needed_issue_stage[UNIT_IDS.MUL];
                tr_div_op <= instruction_issued && unit_needed_issue_stage[UNIT_IDS.DIV];
                tr_misc_op <= instruction_issued & ~(tr_alu_op | tr_branch_or_jump_op | tr_load_op | tr_store_op | tr_mul_op | tr_div_op);
            end
        end

        assign tr_instruction_issued_dec = instruction_issued;
        assign tr_instruction_pc_dec = issue.pc;
        assign tr_instruction_data_dec = issue.instruction;
    end endgenerate

endmodule
