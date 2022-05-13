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
        logic valid;
        logic [31:0] data;
    } wb_packet_t;

    typedef struct packed{
        id_t id;
        logic valid;
        phys_addr_t phys_addr;
        logic [31:0] data;
    } commit_packet_t;

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

    } cva5_trace_events_t;

    typedef struct packed {
        logic [31:0] pc;
        logic [31:0] instruction;
        logic valid;
    } trace_retire_outputs_t;

    typedef struct packed {
        logic [31:0] instruction_pc_dec;
        logic [31:0] instruction_data_dec;
        cva5_trace_events_t events;
    } trace_outputs_t;

endpackage
