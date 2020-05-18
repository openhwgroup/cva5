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
import riscv_types::*;
import taiga_types::*;

module decode_and_issue (
        input logic clk,
        input logic rst,

        output logic pre_decode_pop,
        input logic fb_valid,
        input fetch_buffer_packet_t fb,

        tracking_interface.decode ti,
        register_file_issue_interface.issue rf_issue,

        output alu_inputs_t alu_inputs,
        output load_store_inputs_t ls_inputs,
        output branch_inputs_t branch_inputs,
        output gc_inputs_t gc_inputs,
        output mul_inputs_t mul_inputs,
        output div_inputs_t div_inputs,

        unit_issue_interface.decode unit_issue [NUM_UNITS-1:0],

        input logic gc_issue_hold,
        input logic gc_fetch_flush,
        input logic gc_issue_flush,
        output logic gc_flush_required,


        output logic instruction_issued,
        output logic instruction_issued_no_rd,
        output logic instruction_issued_with_rd,
        output logic illegal_instruction,

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
    logic [4:0] opcode_trim;

    logic uses_rs1;
    logic uses_rs2;
    logic uses_rd;
    logic rd_zero;

    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] rd_addr;

    logic csr_imm_op;
    logic environment_op;
    logic nop;

    logic issue_valid;
    logic operands_ready;
    logic [NUM_UNITS-1:0] unit_operands_ready;
    logic mult_div_op;

    logic [NUM_WB_UNITS-1:0] unit_needed_for_id_gen;
    logic [WB_UNITS_WIDTH-1:0] unit_needed_for_id_gen_int;
    logic [NUM_UNITS-1:0] unit_needed;
    logic [NUM_UNITS-1:0] unit_needed_issue_stage;
    logic [NUM_UNITS-1:0] unit_ready;
    logic [NUM_UNITS-1:0] issue_ready;
    logic [NUM_UNITS-1:0] issue;

    logic illegal_instruction_pattern;

    logic dec_advance;
    logic issue_stage_valid;

    logic [2:0] fn3_issue_stage;
    logic [6:0] opcode_issue_stage;
    logic [4:0] rs1_addr_issue_stage;
    logic [4:0] rs2_addr_issue_stage;
    logic [4:0] rd_addr_issue_stage;
    logic uses_rd_issue_stage;
    logic [31:0] pc_issue_stage;
    logic [31:0] instruction_issue_stage;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    assign dec_advance = (~issue_stage_valid) | instruction_issued;

    always_ff @(posedge clk) begin
        if (rst | gc_fetch_flush)
            issue_stage_valid <= 0;
        else if (dec_advance)
            issue_stage_valid <= fb_valid & ~gc_fetch_flush & ~illegal_instruction_pattern;
    end

    always_ff @(posedge clk) begin
        if (dec_advance) begin
            pc_issue_stage <= fb.pc;
            instruction_issue_stage <= fb.instruction;
            fn3_issue_stage <= fn3;
            opcode_issue_stage <= opcode;
            rs1_addr_issue_stage <= rs1_addr;
            rs2_addr_issue_stage <= rs2_addr;
            rd_addr_issue_stage <= rd_addr;
            uses_rd_issue_stage <= uses_rd;
        end
    end

    ////////////////////////////////////////////////////
    //Instruction Buffer
    assign pre_decode_pop = fb_valid & dec_advance;



    //Instruction aliases
    assign opcode = fb.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn3 = fb.instruction[14:12];
    assign rs1_addr = fb.instruction[19:15];
    assign rs2_addr = fb.instruction[24:20];
    assign rd_addr = fb.instruction[11:7];

    assign csr_imm_op = (opcode_trim == SYSTEM_T) && fn3[2];
    assign environment_op = (opcode_trim == SYSTEM_T) && (fn3 == 0);

    ////////////////////////////////////////////////////
    //Register File Support
    assign uses_rs1 = !(opcode_trim inside {LUI_T, AUIPC_T, JAL_T, FENCE_T} || csr_imm_op || environment_op);
    assign uses_rs2 = opcode_trim inside {BRANCH_T, STORE_T, ARITH_T, AMO_T};
    assign uses_rd = !(opcode_trim inside {BRANCH_T, STORE_T, FENCE_T} || environment_op);

    assign rd_zero = ~|rd_addr;
    assign nop = (opcode_trim inside {LUI_T, AUIPC_T, ARITH_T, ARITH_IMM_T} && rd_zero);

    ////////////////////////////////////////////////////
    //Register File interface inputs
    assign rf_issue.rs1_addr = rs1_addr_issue_stage;
    assign rf_issue.rs2_addr = rs2_addr_issue_stage;
    assign rf_issue.rd_addr = rd_addr_issue_stage;

    always_ff @(posedge clk) begin
        if (dec_advance) begin
            rf_issue.uses_rs1 <= uses_rs1;
            rf_issue.uses_rs2 <= uses_rs2;
        end
    end
    assign rf_issue.instruction_issued = instruction_issued_with_rd & (|rd_addr_issue_stage);
    assign rf_issue.id = ti.issue_id;

    ////////////////////////////////////////////////////
    //Tracking Interface
    //CSR results are passed through the load/store output
    always_comb begin
        unit_needed_for_id_gen = unit_needed[NUM_WB_UNITS-1:0];
        unit_needed_for_id_gen[LS_UNIT_WB_ID] |= (unit_needed[GC_UNIT_ID] & is_csr);
    end
    one_hot_to_integer #(NUM_WB_UNITS) unit_id_gen (.*, .one_hot(unit_needed_for_id_gen), .int_out(unit_needed_for_id_gen_int));

    always_ff @(posedge clk) begin
        if (dec_advance) begin
            ti.inflight_packet.is_store <= is_store;
            ti.issue_unit_id <= unit_needed_for_id_gen_int;
            ti.exception_possible <= opcode_trim inside {LOAD_T, STORE_T, AMO_T};
            ti.inflight_packet.rd_addr <= rd_addr;
        end
    end
    assign ti.issued = instruction_issued & (uses_rd_issue_stage | unit_needed_issue_stage[LS_UNIT_WB_ID]);

    ////////////////////////////////////////////////////
    //Unit Determination
    assign unit_needed[BRANCH_UNIT_ID] = opcode_trim inside {BRANCH_T, JAL_T, JALR_T};
    assign unit_needed[ALU_UNIT_WB_ID] =  ((opcode_trim == ARITH_T) && ~fb.instruction[25]) || (opcode_trim inside {ARITH_IMM_T, AUIPC_T, LUI_T, JAL_T, JALR_T});
    assign unit_needed[LS_UNIT_WB_ID] = opcode_trim inside {LOAD_T, STORE_T, AMO_T};
    assign unit_needed[GC_UNIT_ID] = opcode_trim inside {SYSTEM_T, FENCE_T};

    assign mult_div_op = (opcode_trim == ARITH_T) && fb.instruction[25];
    generate if (USE_MUL)
        assign unit_needed[MUL_UNIT_WB_ID] = mult_div_op && ~fn3[2];
    endgenerate

    generate if (USE_DIV)
        assign unit_needed[DIV_UNIT_WB_ID] = mult_div_op && fn3[2];
    endgenerate

    always_ff @(posedge clk) begin
        if (dec_advance)
            unit_needed_issue_stage <= unit_needed;
    end

    ////////////////////////////////////////////////////
    //Unit ready
    generate for (i=0; i<NUM_UNITS; i++) begin
        assign unit_ready[i] = unit_issue[i].ready;
    end endgenerate

    ////////////////////////////////////////////////////
    //Issue Determination
    assign issue_valid = issue_stage_valid & ti.id_available & ~gc_issue_hold & ~gc_fetch_flush;

    assign operands_ready = ~rf_issue.rs1_conflict & ~rf_issue.rs2_conflict;

    //All units share the same operand ready logic except load-store which has an internal forwarding path
    always_comb begin
        unit_operands_ready = {NUM_UNITS{operands_ready}};
        unit_operands_ready[LS_UNIT_WB_ID] = ~rf_issue.rs1_conflict;
    end

    assign issue_ready = unit_needed_issue_stage & unit_ready;
    assign issue = {NUM_UNITS{issue_valid}} & unit_operands_ready & issue_ready;

    assign instruction_issued = issue_valid & |(unit_operands_ready & issue_ready);
    assign instruction_issued_no_rd = instruction_issued & ~uses_rd_issue_stage;
    assign instruction_issued_with_rd = instruction_issued & uses_rd_issue_stage;


    ////////////////////////////////////////////////////
    //ALU unit inputs
    logic [XLEN-1:0] alu_rs1_data;
    logic [XLEN-1:0] alu_rs2_data;
    alu_rs1_op_t alu_rs1_sel;
    alu_rs1_op_t alu_rs1_sel_r;
    alu_rs2_op_t alu_rs2_sel;
    alu_rs2_op_t alu_rs2_sel_r;

    always_comb begin
        if (opcode_trim inside {ARITH_T, ARITH_IMM_T})
            alu_rs1_sel = ALU_RS1_RF;
        else if (opcode_trim inside {JAL_T, JALR_T, AUIPC_T})//AUIPC JAL JALR
            alu_rs1_sel = ALU_RS1_PC;
        else
            alu_rs1_sel = ALU_RS1_ZERO;//LUI
    end

    always_comb begin
        if (opcode_trim inside {LUI_T, AUIPC_T}) //LUI or AUIPC
            alu_rs2_sel = ALU_RS2_LUI_AUIPC;
        else if (opcode_trim == ARITH_IMM_T) //ARITH_IMM
            alu_rs2_sel = ALU_RS2_ARITH_IMM;
        else if (opcode_trim inside {JAL_T, JALR_T} ) //JAL JALR
            alu_rs2_sel = ALU_RS2_JAL_JALR;
        else
            alu_rs2_sel = ALU_RS2_RF;
    end

    always_ff @(posedge clk) begin
        if (dec_advance) begin
            alu_rs1_sel_r <= alu_rs1_sel;
            alu_rs2_sel_r <= alu_rs2_sel;
        end
    end

    always_comb begin
        case(alu_rs1_sel_r)
            ALU_RS1_ZERO : alu_rs1_data = '0;
            ALU_RS1_PC : alu_rs1_data = pc_issue_stage;
            default : alu_rs1_data = rf_issue.rs1_data; //ALU_RS1_RF
        endcase

        case(alu_rs2_sel_r)
            ALU_RS2_LUI_AUIPC : alu_rs2_data = {instruction_issue_stage[31:12], 12'b0};
            ALU_RS2_ARITH_IMM : alu_rs2_data = 32'(signed'(instruction_issue_stage[31:20]));
            ALU_RS2_JAL_JALR : alu_rs2_data = 4;
            ALU_RS2_RF : alu_rs2_data = rf_issue.rs2_data;
        endcase
    end

    //Add cases: JAL, JALR, LUI, AUIPC, ADD[I], all logic ops
    //sub cases: SUB, SLT[U][I]
    logic sub_instruction;
    assign sub_instruction = (fn3 == ADD_SUB_fn3) && fb.instruction[30] && opcode[5];//If ARITH instruction

    alu_logic_op_t alu_logic_op;
    always_comb begin
        case (fn3)
            SLT_fn3 : alu_logic_op = ALU_LOGIC_ADD;
            SLTU_fn3 : alu_logic_op = ALU_LOGIC_ADD;
            SLL_fn3 : alu_logic_op = ALU_LOGIC_ADD;
            XOR_fn3 : alu_logic_op = ALU_LOGIC_XOR;
            OR_fn3 : alu_logic_op = ALU_LOGIC_OR;
            AND_fn3 : alu_logic_op = ALU_LOGIC_AND;
            SRA_fn3 : alu_logic_op = ALU_LOGIC_ADD;
            ADD_SUB_fn3 : alu_logic_op = ALU_LOGIC_ADD;
        endcase
        //put LUI, AUIPC, JAL and JALR through adder path
        alu_logic_op = opcode[2] ? ALU_LOGIC_ADD : alu_logic_op;
    end

    alu_logic_op_t alu_logic_op_r;
    logic alu_subtract;
    logic alu_lshift;
    logic alu_shifter_path;
    logic alu_slt_path;

    always_ff @(posedge clk) begin
        if (dec_advance) begin
            alu_logic_op_r <= alu_logic_op;
            alu_subtract <= ~opcode[2] & (fn3 inside {SLTU_fn3, SLT_fn3} || sub_instruction);//opcode[2] covers LUI,AUIPC,JAL,JALR
            alu_lshift <= ~fn3[2];
            alu_shifter_path <= ~(opcode[2] | fn3 inside {SLT_fn3, SLTU_fn3, XOR_fn3, OR_fn3, AND_fn3, ADD_SUB_fn3}); //opcode[2] LUI AUIPC JAL JALR
            alu_slt_path <= ~opcode[2] & fn3 inside {SLT_fn3, SLTU_fn3};
        end
    end
    assign alu_inputs.logic_op = alu_logic_op_r;
    assign alu_inputs.subtract = alu_subtract;
    assign alu_inputs.arith = alu_rs1_data[XLEN-1] & instruction_issue_stage[30];//shift in bit
    assign alu_inputs.lshift = alu_lshift;
    assign alu_inputs.shifter_path = alu_shifter_path;
    assign alu_inputs.slt_path = alu_slt_path;


    assign alu_inputs.in1 = {(rf_issue.rs1_data[XLEN-1] & ~fn3_issue_stage[0]), alu_rs1_data};//(fn3[0]  is SLTU_fn3);
    assign alu_inputs.in2 = {(alu_rs2_data[XLEN-1] & ~fn3_issue_stage[0]), alu_rs2_data};
    assign alu_inputs.shifter_in = rf_issue.rs1_data;
    assign alu_inputs.shift_amount = opcode_issue_stage[5] ? rf_issue.rs2_data[4:0] : rs2_addr_issue_stage;

    ////////////////////////////////////////////////////
    //Load Store unit inputs
    logic is_load;
    logic is_store;
    logic amo_op;
    logic store_conditional;
    logic load_reserve;
    logic [4:0] amo_type;

    assign amo_op =  USE_AMO ? (opcode_trim == AMO_T) : 1'b0;
    assign amo_type = fb.instruction[31:27];
    assign store_conditional = (amo_type == AMO_SC);
    assign load_reserve = (amo_type == AMO_LR);

    generate if (USE_AMO) begin
            assign ls_inputs.amo.is_lr = load_reserve;
            assign ls_inputs.amo.is_sc = store_conditional;
            assign ls_inputs.amo.is_amo = amo_op & ~(load_reserve | store_conditional);
            assign ls_inputs.amo.op = amo_type;
        end
        else begin
            assign ls_inputs.amo = '0;
        end
    endgenerate

    assign is_load = (opcode_trim inside {LOAD_T, AMO_T}) && !(amo_op & store_conditional); //LR and AMO_ops perform a read operation as well
    assign is_store = (opcode_trim == STORE_T) || (amo_op && store_conditional);//Used for LS unit and for ID tracking

    logic [11:0] ls_offset;
    logic is_load_r;
    logic is_store_r;
    always_ff @(posedge clk) begin
        if (dec_advance) begin
            ls_offset <= opcode[5] ? {fb.instruction[31:25], fb.instruction[11:7]} : fb.instruction[31:20];
            is_load_r <= is_load;
            is_store_r <= is_store;
        end
    end

    assign ls_inputs.offset = ls_offset;
    assign ls_inputs.load = is_load_r;
    assign ls_inputs.store = is_store_r;
    assign ls_inputs.fn3 = amo_op ? LS_W_fn3 : fn3_issue_stage;
    assign ls_inputs.pc = pc_issue_stage;
    assign ls_inputs.rs1 = rf_issue.rs1_data;
    assign ls_inputs.rs2 = rf_issue.rs2_data;
    assign ls_inputs.forwarded_store = rf_issue.rs2_conflict;
    assign ls_inputs.store_forward_id = rf_issue.rs2_id;

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
    branch_predictor_metadata_t branch_metadata;
    logic branch_prediction_used;
    logic [BRANCH_PREDICTOR_WAYS-1:0] bp_update_way;

    always_ff @(posedge clk) begin
        if (dec_advance) begin
            is_return <= (opcode_trim == JALR_T) && ((rs1_link & ~rd_link) | (rs1_link & rd_link & ~rs1_eq_rd));
            is_call <= (opcode_trim inside {JAL_T, JALR_T}) && rd_link;
            br_use_signed <= !(fn3 inside {BLTU_fn3, BGEU_fn3});

            //Branch Predictor support
            branch_metadata <= fb.branch_metadata;
            branch_prediction_used <= fb.branch_prediction_used;
            bp_update_way <= fb.bp_update_way;
        end
    end

    assign branch_inputs.branch_metadata = branch_metadata;
    assign branch_inputs.branch_prediction_used = branch_prediction_used;
    assign branch_inputs.bp_update_way = bp_update_way;

    assign branch_inputs.is_return = is_return;
    assign branch_inputs.is_call = is_call;
    assign branch_inputs.fn3 = fn3_issue_stage;
    assign branch_inputs.instruction = instruction_issue_stage;
    assign branch_inputs.use_signed = br_use_signed;
    assign branch_inputs.jal = opcode_issue_stage[3];//(opcode == JAL);
    assign branch_inputs.jalr = ~opcode_issue_stage[3] & opcode_issue_stage[2];//(opcode == JALR);


    assign branch_inputs.dec_pc = pc_issue_stage;
    assign branch_inputs.dec_pc_valid = issue_stage_valid;
    assign branch_inputs.rs1 = rf_issue.rs1_data;
    assign branch_inputs.rs2 = rf_issue.rs2_data;


    ////////////////////////////////////////////////////
    //Global Control unit inputs
    logic sfence;
    logic ifence;
    logic is_csr;
    logic is_csr_r;
    logic potential_flush;
    assign sfence = fb.instruction[25];
    assign ifence =  (opcode_trim == FENCE_T) && fn3[0];
    assign is_csr = (opcode_trim == SYSTEM_T) && (fn3 != 0);

    logic is_ecall;
    logic is_ebreak;
    logic is_ret;
    logic is_fence;
    logic is_ifence_r;

    always_ff @(posedge clk) begin
        if (dec_advance) begin
            is_csr_r <= is_csr;
            is_ecall <= ENABLE_M_MODE && environment_op && (fb.instruction[21:20] == 0);
            is_ebreak <= ENABLE_M_MODE && environment_op && (fb.instruction[21:20] == 2'b01);
            is_ret <= ENABLE_M_MODE && environment_op && (fb.instruction[21:20] == 2'b10);
            is_fence <= ENABLE_M_MODE && (opcode_trim == FENCE_T) && ~fn3[0];
            is_ifence_r <= ifence;
            potential_flush <= (environment_op | ifence);
        end
    end

    assign gc_inputs.is_ecall = is_ecall;
    assign gc_inputs.is_ebreak = is_ebreak;
    assign gc_inputs.is_ret = is_ret;
    assign gc_inputs.pc = pc_issue_stage;
    assign gc_inputs.instruction = instruction_issue_stage;
    assign gc_inputs.is_csr = is_csr_r;
    assign gc_inputs.is_fence = is_fence;
    assign gc_inputs.is_i_fence = ENABLE_M_MODE & issue[GC_UNIT_ID] & is_ifence_r;

    assign gc_inputs.rs1 = rf_issue.rs1_data;
    assign gc_inputs.rs2 = rf_issue.rs2_data;
    assign gc_flush_required = ENABLE_M_MODE && issue[GC_UNIT_ID] && potential_flush;

    ////////////////////////////////////////////////////
    //Mul unit inputs
    generate if (USE_MUL) begin
        assign mul_inputs.rs1 = rf_issue.rs1_data;
        assign mul_inputs.rs2 = rf_issue.rs2_data;
        assign mul_inputs.op = fn3_issue_stage[1:0];
    end endgenerate

    ////////////////////////////////////////////////////
    //Div unit inputs
    generate if (USE_DIV) begin
        logic [4:0] prev_div_rs1_addr;
        logic [4:0] prev_div_rs2_addr;
        logic prev_div_result_valid;
        logic set_prev_div_result_valid;
        logic clear_prev_div_result_valid;
        logic current_op_resuses_rs1_rs2;

        always_ff @(posedge clk) begin
            if (issue[DIV_UNIT_WB_ID]) begin
                prev_div_rs1_addr <= rs1_addr;
                prev_div_rs2_addr <= rs2_addr;
            end
        end

        assign current_op_resuses_rs1_rs2 = (prev_div_rs1_addr == rs1_addr_issue_stage) && (prev_div_rs2_addr == rs2_addr_issue_stage);
        assign set_prev_div_result_valid = unit_needed_issue_stage[DIV_UNIT_WB_ID];

        //If current div operation overwrites an input register OR any other instruction overwrites the last div operations input registers
        assign clear_prev_div_result_valid = uses_rd_issue_stage & ((rd_addr_issue_stage == (unit_needed_issue_stage[DIV_UNIT_WB_ID] ? rs1_addr_issue_stage : prev_div_rs1_addr)) || (rd_addr_issue_stage == (unit_needed_issue_stage[DIV_UNIT_WB_ID] ? rs2_addr_issue_stage : prev_div_rs2_addr)));

        set_clr_reg_with_rst #(.SET_OVER_CLR(0), .WIDTH(1), .RST_VALUE(0)) prev_div_result_valid_m (
            .clk, .rst,
            .set(instruction_issued & set_prev_div_result_valid),
            .clr(instruction_issued & clear_prev_div_result_valid),
            .result(prev_div_result_valid)
        );

        assign div_inputs.rs1 = rf_issue.rs1_data;
        assign div_inputs.rs2 = rf_issue.rs2_data;
        assign div_inputs.op = fn3_issue_stage[1:0];
        assign div_inputs.reuse_result = prev_div_result_valid & current_op_resuses_rs1_rs2;
    end endgenerate

    ////////////////////////////////////////////////////
    //Unit EX signals
    generate for (i = 0; i < NUM_UNITS; i++) begin
        assign unit_issue[i].possible_issue = unit_needed_issue_stage[i] & unit_operands_ready[i] & issue_stage_valid & ti.id_available & ~gc_issue_hold;
        assign unit_issue[i].new_request = issue[i];
        assign unit_issue[i].instruction_id = ti.issue_id;
        always_ff @(posedge clk) begin
            unit_issue[i].new_request_r <= issue[i];
        end
    end endgenerate

    ////////////////////////////////////////////////////
    //Illegal Instruction check
    logic illegal_instruction_pattern_r;
    generate if (ENABLE_M_MODE) begin
        illegal_instruction_checker illegal_op_check (
            .instruction(fb.instruction), .illegal_instruction(illegal_instruction_pattern)
        );
        always_ff @(posedge clk) begin
            if (rst)
                illegal_instruction_pattern_r <= 0;
            else if (dec_advance)
                illegal_instruction_pattern_r <= illegal_instruction_pattern;
        end


        //Illegal instruction if the instruction is invalid, but could otherwise be issued
        assign illegal_instruction = illegal_instruction_pattern_r & issue_stage_valid & ti.id_available & ~gc_issue_hold & ~gc_fetch_flush;
    end endgenerate
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin
        assign tr_operand_stall = |(unit_needed_issue_stage & unit_ready) & issue_valid & ~|(unit_operands_ready & issue_ready);
        assign tr_unit_stall = ~|(unit_needed_issue_stage & unit_ready) & issue_valid & |(unit_operands_ready & issue_ready);
        assign tr_no_id_stall = |(unit_needed_issue_stage & unit_ready) & (issue_stage_valid & ~ti.id_available & ~gc_issue_hold & ~gc_fetch_flush) & |(unit_operands_ready & issue_ready);
        assign tr_no_instruction_stall = ~issue_stage_valid | gc_fetch_flush;
        assign tr_other_stall = issue_stage_valid & ~instruction_issued & ~(tr_operand_stall | tr_unit_stall | tr_no_id_stall | tr_no_instruction_stall);
        assign tr_branch_operand_stall = tr_operand_stall & unit_needed_issue_stage[BRANCH_UNIT_ID];
        assign tr_alu_operand_stall = tr_operand_stall & unit_needed_issue_stage[ALU_UNIT_WB_ID] & ~unit_needed_issue_stage[BRANCH_UNIT_ID];
        assign tr_ls_operand_stall = tr_operand_stall & unit_needed_issue_stage[LS_UNIT_WB_ID];
        assign tr_div_operand_stall = tr_operand_stall & unit_needed_issue_stage[DIV_UNIT_WB_ID];

        //Instruction Mix
        always_ff @(posedge clk) begin
            if (dec_advance) begin
                tr_alu_op <= instruction_issued && (opcode_trim inside {ARITH_T, ARITH_IMM_T, AUIPC_T, LUI_T} && ~tr_mul_op && ~tr_div_op);
                tr_branch_or_jump_op <= instruction_issued && (opcode_trim inside {JAL_T, JALR_T, BRANCH_T});
                tr_load_op <= instruction_issued && (opcode_trim inside {LOAD_T, AMO_T});
                tr_store_op <= instruction_issued && (opcode_trim inside {STORE_T});
                tr_mul_op <= instruction_issued && unit_needed_issue_stage[MUL_UNIT_WB_ID];
                tr_div_op <= instruction_issued && unit_needed_issue_stage[DIV_UNIT_WB_ID];
                tr_misc_op <= instruction_issued & ~(tr_alu_op | tr_branch_or_jump_op | tr_load_op | tr_store_op | tr_mul_op | tr_div_op);
            end
        end

        assign tr_instruction_issued_dec = instruction_issued;
        assign tr_instruction_pc_dec = pc_issue_stage;
        assign tr_instruction_data_dec = instruction_issue_stage;
    end endgenerate

endmodule
