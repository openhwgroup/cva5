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

package cva5_types;
    import cva5_config::*;
    import riscv_types::*;
    import csr_types::*;

    localparam LOG2_RETIRE_PORTS = $clog2(RETIRE_PORTS);
    localparam LOG2_MAX_IDS = $clog2(MAX_IDS);

    typedef logic[LOG2_MAX_IDS-1:0] id_t;
    typedef logic[1:0] branch_predictor_metadata_t;

    typedef logic [3:0] addr_hash_t;
    typedef logic [5:0] phys_addr_t;

    typedef enum logic [1:0] {
        ALU_CONSTANT = 2'b00,
        ALU_ADD_SUB = 2'b01,
        ALU_SLT = 2'b10,
        ALU_SHIFT = 2'b11
    } alu_op_t;

    typedef enum logic [1:0] {
        ALU_LOGIC_XOR = 2'b00,
        ALU_LOGIC_OR = 2'b01,
        ALU_LOGIC_AND = 2'b10,
        ALU_LOGIC_ADD = 2'b11
    } alu_logic_op_t;

    typedef struct packed{
        logic valid;
        exception_code_t code;
        logic [31:0] tval;
        logic [31:0] pc;
        id_t id;
    } exception_packet_t;

    typedef struct packed{
        logic ok;
        exception_code_t error_code;
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

        rs_addr_t rd_addr;
        phys_addr_t phys_rd_addr;

        logic uses_rd;
        logic is_multicycle;
        id_t id;
        exception_sources_t exception_unit;
        logic stage_valid;
        fetch_metadata_t fetch_metadata;
    } issue_packet_t;

    typedef struct packed{
        logic [XLEN:0] in1;//contains sign padding bit for slt operation
        logic [XLEN:0] in2;//contains sign padding bit for slt operation
        logic [XLEN-1:0] shifter_in;
        logic [31:0] constant_adder;
        alu_op_t alu_op;
        alu_logic_op_t logic_op;
        logic [4:0] shift_amount;
        logic subtract;
        logic arith;//contains sign padding bit for arithmetic shift right operation
        logic lshift;
    } alu_inputs_t;

    typedef struct packed {
        logic [XLEN:0] rs1;
        logic [XLEN:0] rs2;
        logic [31:0] pc_p4;
        logic [2:0] fn3;
        logic [31:0] issue_pc;
        logic issue_pc_valid;
        logic jal;
        logic jalr;
        logic jal_jalr;
        logic is_call;
        logic is_return;
        logic [20:0] pc_offset;
    } branch_inputs_t;

    typedef struct packed {
        id_t id;
        logic valid;
        logic [31:0] pc;
        logic [31:0] target_pc;
        logic branch_taken;
        logic is_branch;
        logic is_return;
        logic is_call;
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
        logic fence;
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
        csr_addr_t addr;
        logic[1:0] op;
        logic reads;
        logic writes;
        logic [XLEN-1:0] data;
    } csr_inputs_t;

    typedef struct packed{
        logic [31:0] pc_p4;
        logic is_ifence;
        logic is_mret;
        logic is_sret;
    } gc_inputs_t;

    typedef struct packed {
        logic [31:0] addr;
        logic load;
        logic store;
        logic [3:0] be;
        logic [2:0] fn3;
        logic [31:0] data;
        id_t id;
        phys_addr_t phys_addr;
        logic forwarded_store;
        id_t id_needed;
    } lsq_entry_t;

    typedef struct packed {
        logic [31:0] addr;
        logic [3:0] be;
        logic [2:0] fn3;
        logic forwarded_store;
        logic [31:0] data;
    } sq_entry_t;

    typedef struct packed {
        logic sq_empty;
        logic no_released_stores_pending;
        logic idle;
    } load_store_status_t;

    typedef struct packed{
        id_t id;
        phys_addr_t phys_addr;
        logic valid;
        logic [31:0] data;
    } wb_packet_t;

    typedef struct packed{
        logic valid;
        id_t phys_id;
        logic [LOG2_RETIRE_PORTS : 0] count;
    } retire_packet_t;

    typedef struct packed {
        logic [31:0] addr;
        logic load;
        logic store;
        logic [3:0] be;
        logic [2:0] fn3;
        logic [31:0] data_in;
        id_t id;
        phys_addr_t phys_addr;
    } data_access_shared_inputs_t;

    typedef enum  {
        LUTRAM_FIFO,
        NON_MUXED_INPUT_FIFO,
        NON_MUXED_OUTPUT_FIFO
    } fifo_type_t;

    typedef struct packed{
        logic init_clear;
        logic fetch_hold;
        logic issue_hold;
        logic fetch_flush;
        logic writeback_supress;
        logic retire_hold;
        logic sq_flush;
        logic tlb_flush;
        logic exception_pending;
        exception_packet_t exception;
        logic pc_override;
        logic [31:0] pc;
    } gc_outputs_t;

    typedef struct packed {
        logic software;
        logic timer;
        logic external;
    } interrupt_t;
    
    typedef enum {
        FETCH_EARLY_BR_CORRECTION_STAT,
        FETCH_SUB_UNIT_STALL_STAT,
        FETCH_ID_STALL_STAT,
        FETCH_IC_HIT_STAT,
        FETCH_IC_MISS_STAT,
        FETCH_IC_ARB_STALL_STAT,

        FETCH_BP_BR_CORRECT_STAT,
        FETCH_BP_BR_MISPREDICT_STAT,
        FETCH_BP_RAS_CORRECT_STAT,
        FETCH_BP_RAS_MISPREDICT_STAT,

        ISSUE_NO_INSTRUCTION_STAT,
        ISSUE_NO_ID_STAT,
        ISSUE_FLUSH_STAT,
        ISSUE_UNIT_BUSY_STAT,
        ISSUE_OPERANDS_NOT_READY_STAT,
        ISSUE_HOLD_STAT,
        ISSUE_MULTI_SOURCE_STAT,
        ISSUE_OPERAND_STALL_ON_LOAD_STAT,
        ISSUE_OPERAND_STALL_ON_MULTIPLY_STAT,
        ISSUE_OPERAND_STALL_ON_DIVIDE_STAT,
        ISSUE_OPERAND_STALL_FOR_BRANCH_STAT,
        ISSUE_STORE_WITH_FORWARDED_DATA_STAT,
        ISSUE_DIVIDER_RESULT_REUSE_STAT,

        LSU_LOAD_BLOCKED_BY_STORE_STAT,
        LSU_SUB_UNIT_STALL_STAT,
        LSU_DC_HIT_STAT,
        LSU_DC_MISS_STAT,
        LSU_DC_ARB_STALL_STAT
    } stats_t;

    typedef enum {
        ALU_STAT,
        BR_STAT,
        MUL_STAT,
        DIV_STAT,
        LOAD_STAT,
        STORE_STAT,
        MISC_STAT
    } instruction_mix_stats_t;

    typedef struct packed {
        logic [31:0] pc;
        logic [31:0] instruction;
        logic valid;
    } trace_retire_outputs_t;

endpackage
