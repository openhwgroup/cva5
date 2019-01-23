/*
 * Copyright © 2017, 2018 Eric Matthews,  Lesley Shannon
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

    parameter INFLIGHT_QUEUE_WIDTH = $clog2(INFLIGHT_QUEUE_DEPTH);

    typedef enum bit [6:0] {
        LUI = 7'b0110111,
        AUIPC = 7'b0010111,
        JAL = 7'b1101111,
        JALR = 7'b1100111,
        BRANCH = 7'b1100011,
        LOAD = 7'b0000011,
        STORE = 7'b0100011,
        ARITH_IMM = 7'b0010011,
        ARITH = 7'b0110011,//includes mul/div
        FENCE = 7'b0001111,
        AMO = 7'b0101111,
        SYSTEM = 7'b1110011
        //end of RV32I
    } opcodes_t;

    typedef enum bit [4:0] {
        LUI_T = 5'b01101,
        AUIPC_T = 5'b00101,
        JAL_T = 5'b11011,
        JALR_T = 5'b11001,
        BRANCH_T = 5'b11000,
        LOAD_T = 5'b00000,
        STORE_T = 5'b01000,
        ARITH_IMM_T = 5'b00100,
        ARITH_T = 5'b01100,//includes mul/div
        FENCE_T = 5'b00011,
        AMO_T = 5'b01011,
        SYSTEM_T = 5'b11100,
        //end of RV32I
        CUSTOM_T = 5'b11110
    } opcodes_trimmed_t;

    typedef enum bit [2:0] {
        ADD_SUB_fn3 = 3'b000,
        SLL_fn3 = 3'b001,
        SLT_fn3 = 3'b010,
        SLTU_fn3 = 3'b011,
        XOR_fn3 = 3'b100,
        OR_fn3 = 3'b110,
        SRA_fn3 = 3'b101,
        AND_fn3 = 3'b111
    } fn3_arith_t;


    typedef enum bit [1:0] {
        ALU_LOGIC_XOR = 2'b00,
        ALU_LOGIC_OR = 2'b01,
        ALU_LOGIC_AND =2'b10,
        ALU_LOGIC_ADD = 2'b11
    } alu_logic_op_t;

    typedef enum bit [1:0] {
        ALU_ADD_SUB = 2'b00,
        ALU_SLT = 2'b01,
        ALU_RSHIFT =2'b10,
        ALU_LSHIFT =2'b11
    } alu_op_t;

    typedef enum bit [2:0] {
        LS_B_fn3 = 3'b000,
        LS_H_fn3 = 3'b001,
        LS_W_fn3 = 3'b010,
        //unused 011
        L_BU_fn3 = 3'b100,
        L_HU_fn3 = 3'b101
        //unused 110
        //unused 111
    } fn3_ls_t;

    typedef enum bit [2:0] {
        BEQ_fn3 = 3'b000,
        BNE_fn3 = 3'b001,
        //010 unused
        //011 unused
        BLT_fn3 = 3'b100,
        BGE_fn3 = 3'b101,
        BLTU_fn3 = 3'b110,
        BGEU_fn3 = 3'b111
    } fn3_branch_t;


    typedef enum bit [2:0] {
        MUL_fn3 = 3'b000,
        MULH_fn3 = 3'b001,
        MULHSU_fn3 = 3'b010,
        MULHU_fn3 = 3'b011,
        DIV_fn3 = 3'b100,
        DIVU_fn3 = 3'b101,
        REM_fn3 = 3'b110,
        REMU_fn3 = 3'b111
    } fn3_mul_div_t;

    typedef enum bit [11:0] {
        //Machine info
        MVENDORID = 12'hF11,
        MARCHID = 12'hF12,
        MIMPID = 12'hF13,
        MHARTID = 12'hF14,
        //Machine trap setup
        MSTATUS = 12'h300,
        MISA = 12'h301,
        MEDELEG = 12'h302,
        MIDELEG = 12'h303,
        MIE = 12'h304,
        MTVEC = 12'h305,
        //Machine trap handling
        MSCRATCH = 12'h340,
        MEPC = 12'h341,
        MCAUSE = 12'h342,
        MTVAL = 12'h343,
        MIP = 12'h344,

        //Machine Counters
        MCYCLE = 12'hB00,
        MINSTRET = 12'hB02,
        MCYCLEH = 12'hB80,
        MINSTRETH = 12'hB82,

        //Supervisor regs
        //Supervisor Trap Setup
        SSTATUS = 12'h100,
        SEDELEG = 12'h102,
        SIDELEG = 12'h103,
        SIE = 12'h104,
        STVEC = 12'h105,

        //Supervisor trap handling
        SSCRATCH = 12'h140,
        SEPC = 12'h141,
        SCAUSE = 12'h142,
        STVAL = 12'h143,
        SIP = 12'h144,

        //Supervisor address translation and protection
        SATP = 12'h180,

        //User regs
        //USER Floating Point
        FFLAGS = 12'h001,
        FRM = 12'h002,
        FCSR = 12'h003,
        //User Counter Timers
        CYCLE = 12'hC00,
        TIME = 12'hC01,
        INSTRET = 12'hC02,
        CYCLEH = 12'hC80,
        TIMEH = 12'hC81,
        INSTRETH = 12'hC82,

        //Debug regs
        DCSR = 12'h7B0,
        DPC = 12'h7B1,
        DSCRATCH = 12'h7B2
    } csr_t;

    typedef enum bit [2:0] {
        NONCSR_fn3 = 3'b000,
        RW_fn3 = 3'b001,
        RS_fn3 = 3'b010,
        RC_fn3 = 3'b011,
        // unused  3'b100,
        RWI_fn3 = 3'b101,
        RSI_fn3 = 3'b110,
        RCI_fn3 = 3'b111
    } fn3_csr_t;

    typedef enum bit [1:0] {
        CSR_RW = 2'b01,
        CSR_RS = 2'b10,
        CSR_RC = 2'b11
    } csr_op_t;

    const bit[1:0] CSR_READ_ONLY = 2'b11;

    typedef enum logic [1:0] {
        USER_PRIV = 2'b00,
        SUPERVISOR_PRIV = 2'b01,
        //reserved
        MACHINE_PRIV = 2'b11
    } privilege_t;


    typedef enum bit [4:0] {
        BARE = 5'd0,
        SV32 = 5'd8
    } vm_t;

    parameter ASIDLEN = 9;//pid

    typedef enum bit [4:0] {
        INST_ADDR_MISSALIGNED = 5'd0,
        INST_ACCESS_FAULT = 5'd1,
        ILLEGAL_INST = 5'd2,
        BREAK = 5'd3,
        LOAD_ADDR_MISSALIGNED = 5'd4,
        LOAD_FAULT = 5'd5,
        STORE_AMO_ADDR_MISSALIGNED = 5'd6,
        STORE_AMO_FAULT = 5'd7,
        ECALL_U = 5'd8,
        ECALL_S = 5'd9,
        //reserved
        ECALL_M = 5'd11,
        INST_PAGE_FAULT = 5'd12,
        LOAD_PAGE_FAULT = 5'd13,
        //reserved
        STORE_OR_AMO_PAGE_FAULT = 5'd15
        //reserved
    } exception_code_t;
    parameter ECODE_W = 5;


    typedef enum bit [4:0] {
        U_SOFTWARE_INTERRUPT = 5'd0,
        S_SOFTWARE_INTERRUPT = 5'd1,
        //RESERVED
        M_SOFTWARE_INTERRUPT = 5'd3,
        U_TIMER_INTERRUPT = 5'd4,
        S_TIMER_INTERRUPT = 5'd5,
        //RESERVED
        M_TIMER_INTERRUPT = 5'd7,
        U_EXTERNAL_INTERRUPT = 5'd8,
        S_EXTERNAL_INTERRUPT = 5'd9,
        //RESERVED
        M_EXTERNAL_INTERRUPT = 5'd11
    } interrupt_code_t;

    typedef logic[INFLIGHT_QUEUE_WIDTH-1:0] instruction_id_t;


    typedef struct packed{
        logic [WB_UNITS_WIDTH-1:0] unit_id;
        instruction_id_t id;
        logic [4:0] rd_addr;
        logic rd_addr_nzero;
    } inflight_queue_packet;

    typedef struct packed{
        logic [31:0] instruction;
        logic [31:0] pc;
        logic uses_rs1;
        logic uses_rs2;
        logic uses_rd;
        logic rd_zero;
        logic is_call;
        logic is_return;
    } instruction_buffer_packet;


    typedef struct packed{
        logic [XLEN:0] in1;//contains sign padding bit for slt operation
        logic [XLEN:0] in2;//contains sign padding bit for slt operation
        logic [XLEN-1:0] shifter_in;
        logic subtract;
        logic arith;//contains sign padding bit for arithmetic shift right operation
        logic lshift;
        logic [1:0] logic_op;
        logic [1:0] op;
    }alu_inputs_t;

    typedef struct packed{
        logic [XLEN-1:0] rs1;
        logic [XLEN-1:0] rs2;
        logic [2:0] fn3;
        logic [31:0] dec_pc;
        logic use_signed;
        logic jal;
        logic jalr;
        logic uses_rd;
        logic is_call;
        logic is_return;
        logic [31:0] instruction;
    } branch_inputs_t;


    typedef enum bit [4:0] {
        AMO_LR = 5'b00010,
        AMO_SC = 5'b00011,
        AMO_SWAP = 5'b00001,
        AMO_ADD = 5'b00000,
        AMO_XOR = 5'b00100,
        AMO_AND = 5'b01100,
        AMO_OR = 5'b01000,
        AMO_MIN = 5'b10000,
        AMO_MAX = 5'b10100,
        AMO_MINU = 5'b11000,
        AMO_MAXU = 5'b11100
    } amo_t;

    typedef struct packed{
        logic [XLEN-1:0] rs1_load;
        logic [XLEN-1:0] rs2;
        logic [4:0] op;
    }amo_alu_inputs_t;


    typedef struct packed{
        logic [XLEN-1:0] virtual_address;
        logic [11:0] offset;
        logic [XLEN-1:0] rs2;
        logic [2:0] fn3;
        logic [4:0] amo;
        logic is_amo;
        logic load;
        logic store;
        logic load_store_forward;
        //exception support
        logic [31:0] pc;
        instruction_id_t id;
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
        logic [31:0] dec_pc;
        logic [31:0] pc;
        logic [XLEN-1:0] rs1;
        logic [XLEN-1:0] rs2;
        logic [6:0] funct7;
        logic [11:0] funct12;
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
        logic load;
        logic store;
        logic [3:0] be;
        logic [2:0] fn3;
        logic [31:0] data_in;
    } data_access_shared_inputs_t;

    typedef enum  {
        LUTRAM_FIFO,
        NON_MUXED_INPUT_FIFO,
        NON_MUXED_OUTPUT_FIFO
    } fifo_type_t;

    //Assembly register definitions for simulation purposes
    typedef struct packed{
        logic [XLEN-1:0] zero;
        logic [XLEN-1:0] ra;
        logic [XLEN-1:0] sp;
        logic [XLEN-1:0] gp;
        logic [XLEN-1:0] tp;
        logic [XLEN-1:0] t0;
        logic [XLEN-1:0] t1;
        logic [XLEN-1:0] t2;
        logic [XLEN-1:0] s0_fp;
        logic [XLEN-1:0] s1;
        logic [XLEN-1:0] a0;
        logic [XLEN-1:0] a1;
        logic [XLEN-1:0] a2;
        logic [XLEN-1:0] a3;
        logic [XLEN-1:0] a4;
        logic [XLEN-1:0] a5;
        logic [XLEN-1:0] a6;
        logic [XLEN-1:0] a7;
        logic [XLEN-1:0] s2;
        logic [XLEN-1:0] s3;
        logic [XLEN-1:0] s4;
        logic [XLEN-1:0] s5;
        logic [XLEN-1:0] s6;
        logic [XLEN-1:0] s7;
        logic [XLEN-1:0] s8;
        logic [XLEN-1:0] s9;
        logic [XLEN-1:0] s10;
        logic [XLEN-1:0] s11;
        logic [XLEN-1:0] t3;
        logic [XLEN-1:0] t4;
        logic [XLEN-1:0] t5;
        logic [XLEN-1:0] t6;
    } simulation_named_regfile;
endpackage
