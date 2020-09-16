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

package taiga_types;
    import taiga_config::*;
    import riscv_types::*;

    localparam MAX_COMPLETE_COUNT = 3 + COMMIT_PORTS; //Branch + Store + System + COMMIT_PORTS

    localparam WB_UNITS_WIDTH = $clog2(NUM_WB_UNITS);
    localparam LOG2_COMMIT_PORTS = $clog2(COMMIT_PORTS);
    localparam LOG2_MAX_IDS = $clog2(MAX_IDS);

    typedef logic[LOG2_MAX_IDS-1:0] id_t;
    typedef logic[WB_UNITS_WIDTH-1:0] unit_id_t;
    typedef logic[1:0] branch_predictor_metadata_t;

    typedef logic [3:0] addr_hash_t;

    typedef enum logic [1:0] {
        ALU_LOGIC_XOR = 2'b00,
        ALU_LOGIC_OR = 2'b01,
        ALU_LOGIC_AND =2'b10,
        ALU_LOGIC_ADD = 2'b11
    } alu_logic_op_t;

    typedef enum logic [1:0] {
        ALU_ADD_SUB = 2'b00,
        ALU_SLT = 2'b01,
        ALU_RSHIFT =2'b10,
        ALU_LSHIFT =2'b11
    } alu_op_t;

    typedef enum logic [1:0] {
        ALU_RS1_ZERO = 2'b00,
        ALU_RS1_PC = 2'b01,
        ALU_RS1_RF =2'b10
    } alu_rs1_op_t;

    typedef enum logic [1:0] {
        ALU_RS2_LUI_AUIPC = 2'b00,
        ALU_RS2_ARITH_IMM = 2'b01,
        ALU_RS2_JAL_JALR = 2'b10,
        ALU_RS2_RF =2'b11
    } alu_rs2_op_t;

    typedef struct packed{
        logic valid;
        exception_code_t code;
        logic [31:0] tval;
        id_t id;
    } exception_packet_t;

    typedef struct packed{
        branch_predictor_metadata_t branch_predictor_metadata;
        logic branch_prediction_used;
        logic [BRANCH_PREDICTOR_WAYS-1:0] branch_predictor_update_way;
    } branch_metadata_t;

    typedef enum logic {
        FETCH_ACCESS_FAULT = 1'b0,
        FETCH_PAGE_FAULT = 1'b1
    } fetch_error_codes_t;

    typedef struct packed{
        logic ok;
        fetch_error_codes_t error_code;
    } fetch_metadata_t;

    typedef struct packed{
        id_t id;
        logic [31:0] pc;
        logic [31:0] instruction;
        logic valid;
        fetch_metadata_t fetch_metadata;
    } decode_packet_t;

    typedef struct packed{
        logic [31:0] pc;
        logic [31:0] instruction;
        logic [2:0] fn3;
        logic [6:0] opcode;

        rs_addr_t [REGFILE_READ_PORTS-1:0] rs_addr;//packed style instead of unpacked due to tool limitations
        logic [4:0] rd_addr;

        logic uses_rs1;
        logic uses_rs2;
        logic uses_rd;
        id_t id;
        logic stage_valid;
        fetch_metadata_t fetch_metadata;
    } issue_packet_t;

    typedef struct packed{
        logic [XLEN:0] in1;//contains sign padding bit for slt operation
        logic [XLEN:0] in2;//contains sign padding bit for slt operation
        logic [XLEN-1:0] shifter_in;
        logic [4:0] shift_amount;
        logic subtract;
        logic arith;//contains sign padding bit for arithmetic shift right operation
        logic lshift;
        alu_logic_op_t logic_op;
        logic shifter_path;
        logic slt_path;
    } alu_inputs_t;

    typedef struct packed {
        logic [XLEN-1:0] rs1;
        logic [XLEN-1:0] rs2;
        logic [2:0] fn3;
        logic [31:0] issue_pc;
        logic issue_pc_valid;
        logic use_signed;
        logic jal;
        logic jalr;
        logic is_call;
        logic is_return;
        logic [20:0] pc_offset;
    } branch_inputs_t;

    typedef struct packed {
        logic[31:0] pc_ex;
        logic [31:0] new_pc;
        logic branch_taken;
        logic branch_ex;
        logic is_branch_ex;
        logic is_return_ex;
        logic is_call_ex;
    } branch_results_t;

    typedef struct packed{
        logic [XLEN-1:0] rs1_load;
        logic [XLEN-1:0] rs2;
        logic [4:0] op;
    }amo_alu_inputs_t;

    typedef struct packed{
        logic is_lr;
        logic is_sc;
        logic is_amo;
        logic [4:0] op;
    } amo_details_t;

    typedef struct packed{
        logic [XLEN-1:0] rs1;
        logic [XLEN-1:0] rs2;
        logic [11:0] offset;
        logic [2:0] fn3;
        logic load;
        logic store;
        logic forwarded_store;
        id_t store_forward_id;
        //amo support
        amo_details_t amo;
    } load_store_inputs_t;

    typedef struct packed{
        logic [XLEN-1:0] rs1;
        logic [XLEN-1:0] rs2;
        logic [1:0] op;
    } mul_inputs_t;

    typedef struct packed{
        logic [XLEN-1:0] rs1;
        logic [XLEN-1:0] rs2;
        logic [1:0] op;
        logic reuse_result;
    } div_inputs_t;

    typedef struct packed{
        logic [XLEN-1:0] rs1;
        logic [11:0] csr_addr;
        logic [1:0] csr_op;
        logic rs1_is_zero;
        logic rd_is_zero;
    } csr_inputs_t;

    typedef struct packed{
        logic [31:0] pc;
        logic [31:0] instruction;
        logic [XLEN-1:0] rs1;
        logic [XLEN-1:0] rs2;
        logic is_csr;
        logic is_fence;
        logic is_i_fence;
        logic is_ecall;
        logic is_ebreak;
        logic is_ret;
    } gc_inputs_t;

    typedef struct packed{
        logic [31:2] addr;
        logic [31:0] data;
        logic rnw;
        logic [0:3] be;
        logic [2:0] size;
        logic con;
    } to_l1_arbiter_packet;

    typedef struct packed {
        logic [31:0] addr;
        logic [2:0] fn3;
        id_t id;
        logic [3:0] potential_store_conflicts;
    } lq_entry_t;

    typedef struct packed {
        logic [31:0] addr;
        logic [3:0] be;
        logic [2:0] fn3;
    } sq_entry_t;

    typedef struct packed {
        logic [31:0] data;
        id_t id;
        logic valid;
    } wb_packet_t;

    typedef struct packed {
        logic [31:0] addr;
        logic load;
        logic store;
        logic [3:0] be;
        logic [2:0] fn3;
        logic [31:0] data_in;
        id_t id;
    } data_access_shared_inputs_t;

    typedef enum  {
        LUTRAM_FIFO,
        NON_MUXED_INPUT_FIFO,
        NON_MUXED_OUTPUT_FIFO
    } fifo_type_t;

    typedef struct packed {
        //Fetch
        logic early_branch_correction;

        //Decode
        logic operand_stall;
        logic unit_stall;
        logic no_id_stall;
        logic no_instruction_stall;
        logic other_stall;
        logic instruction_issued_dec;
        logic branch_operand_stall;
        logic alu_operand_stall;
        logic ls_operand_stall;
        logic div_operand_stall;

        //Instruction mix
        logic alu_op;
        logic branch_or_jump_op;
        logic load_op;
        logic store_op;
        logic mul_op;
        logic div_op;
        logic misc_op;

        //Branch Unit
        logic branch_correct;
        logic branch_misspredict;
        logic return_correct;
        logic return_misspredict;

        //Load Store Unit
        logic load_conflict_delay;

        //Register File
        logic rs1_forwarding_needed;
        logic rs2_forwarding_needed;
        logic rs1_and_rs2_forwarding_needed;

        //Writeback
        unit_id_t num_instructions_completing;
        id_t num_instructions_in_flight;
        id_t num_of_instructions_pending_writeback;
    } taiga_trace_events_t;

    typedef struct packed {
        logic [31:0] instruction_pc_dec;
        logic [31:0] instruction_data_dec;
        taiga_trace_events_t events;
    } trace_outputs_t;

endpackage
