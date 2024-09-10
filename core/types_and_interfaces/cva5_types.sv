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
    localparam MAX_LS_SUBUNITS = 3;

    typedef logic[LOG2_MAX_IDS-1:0] id_t;
    typedef logic[$clog2(MAX_LS_SUBUNITS)-1:0] ls_subunit_t;

    typedef logic [3:0] addr_hash_t;
    typedef logic [5:0] phys_addr_t;

    typedef enum logic [1:0] {
        ALU_CONSTANT = 2'b00,
        ALU_ADD_SUB = 2'b01,
        ALU_SLT = 2'b10,
        ALU_SHIFT = 2'b11
    } alu_op_t;

    typedef struct packed{
        logic valid;
        logic possible;
        logic [NUM_EXCEPTION_SOURCES-1:0] source;
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
        logic [31:0] pc_r;
        logic [31:0] instruction;
        logic [31:0] instruction_r;
        logic [2:0] fn3;
        logic [6:0] opcode;

        rs_addr_t rd_addr;
        phys_addr_t phys_rd_addr;
        phys_addr_t fp_phys_rd_addr;

        logic uses_rd;
        logic fp_uses_rd;
        logic is_multicycle;
        id_t id;
        logic stage_valid;
        fetch_metadata_t fetch_metadata;
    } issue_packet_t;

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

    typedef struct packed {
        logic [11:0] offset;
        logic load;
        logic store;
        logic cache_op;
        logic amo;
        amo_t amo_type;
        logic [3:0] be;
        logic [2:0] fn3;
        logic [31:0] data;
        id_t id;
        id_t id_needed;
        logic fp;
        logic double;
        logic [FLEN-1:0] fp_data;
    } lsq_entry_t;

    typedef struct packed {
        logic [19:0] addr;
        logic rnw;
        logic discard;
        ls_subunit_t subunit;
    } lsq_addr_entry_t;

    typedef struct packed {
        logic [11:0] offset;
        logic [3:0] be;
        logic cache_op;
        logic [31:0] data;
        logic fp;
        logic double;
        logic [FLEN-1:0] fp_data;
    } sq_entry_t;

    typedef struct packed {
        logic outstanding_store;
        logic idle;
    } load_store_status_t;

    typedef struct packed{
        id_t id;
        logic valid;
        logic [31:0] data;
    } wb_packet_t;

    typedef struct packed {
        id_t id;
        logic valid;
        logic[FLEN-1:0] data;
    } fp_wb_packet_t;

    typedef struct packed{
        id_t id;
        logic valid;
    } retire_packet_t;

    typedef enum logic[1:0] {
        INT_DONE,
        SINGLE_DONE,
        DOUBLE_HOLD,
        DOUBLE_DONE
    } fp_ls_op_t;

    typedef struct packed {
        logic [31:0] addr;
        logic load;
        logic store;
        logic cache_op;
        logic amo;
        amo_t amo_type;
        logic [3:0] be;
        logic [2:0] fn3;
        ls_subunit_t subunit;
        logic [31:0] data_in;
        id_t id;
        fp_ls_op_t fp_op;
    } data_access_shared_inputs_t;

    typedef struct packed {
        logic valid;
        logic asid_only;
        logic[ASIDLEN-1:0] asid;
        logic addr_only;
        logic[31:0] addr;
    } tlb_packet_t;

    typedef struct packed{
        logic init_clear;
        logic fetch_hold;
        logic issue_hold;
        logic fetch_flush;
        logic fetch_ifence;
        logic writeback_suppress;
        logic rename_revert;
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
        FPU_STAT,
        MISC_STAT
    } instruction_mix_stats_t;

    typedef struct packed {
        logic [31:0] pc;
        logic [31:0] instruction;
        logic valid;
    } trace_retire_outputs_t;

endpackage
