/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
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

package riscv_types;
    import cva5_config::*;

    localparam XLEN = 32;
    localparam PAGE_ADDR_W = 12;
    localparam ECODE_W = 5;

    typedef logic [4:0] rs_addr_t;

    typedef struct packed {
        logic [6:0] fn7;
        logic [4:0] rs2_addr;
        logic [4:0] rs1_addr;
        logic [2:0] fn3;
        logic [4:0] rd_addr;
        logic [6:0] opcode;
    } common_instruction_t;

    typedef enum logic [4:0] {
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

    typedef enum logic [2:0] {
        ADD_SUB_fn3 = 3'b000,
        SLL_fn3 = 3'b001,
        SLT_fn3 = 3'b010,
        SLTU_fn3 = 3'b011,
        XOR_fn3 = 3'b100,
        OR_fn3 = 3'b110,
        SRA_fn3 = 3'b101,
        AND_fn3 = 3'b111
    } fn3_arith_t;

    typedef enum logic [2:0] {
        LS_B_fn3 = 3'b000,
        LS_H_fn3 = 3'b001,
        LS_W_fn3 = 3'b010,
        //unused 011
        L_BU_fn3 = 3'b100,
        L_HU_fn3 = 3'b101
        //unused 110
        //unused 111
    } fn3_ls_t;

    typedef enum logic [2:0] {
        BEQ_fn3 = 3'b000,
        BNE_fn3 = 3'b001,
        //010 unused
        //011 unused
        BLT_fn3 = 3'b100,
        BGE_fn3 = 3'b101,
        BLTU_fn3 = 3'b110,
        BGEU_fn3 = 3'b111
    } fn3_branch_t;

    typedef enum logic [2:0] {
        MUL_fn3 = 3'b000,
        MULH_fn3 = 3'b001,
        MULHSU_fn3 = 3'b010,
        MULHU_fn3 = 3'b011,
        DIV_fn3 = 3'b100,
        DIVU_fn3 = 3'b101,
        REM_fn3 = 3'b110,
        REMU_fn3 = 3'b111
    } fn3_mul_div_t;

    typedef enum logic [11:0] {
        ECALL_imm = 12'b000000000000,
        EBREAK_imm = 12'b000000000001,
        URET_imm = 12'b000000000010,
        SRET_imm = 12'b000100000010,
        MRET_imm = 12'b001100000010,
        SFENCE_imm = 12'b0001001?????
    } imm_sys_t;

    typedef enum logic [11:0] {
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
        MCOUNTEREN = 12'h306,
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
        SCOUNTEREN = 12'h106,
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
    } csr_reg_addr_t;

    typedef enum logic [2:0] {
        NONCSR_fn3 = 3'b000,
        RW_fn3 = 3'b001,
        RS_fn3 = 3'b010,
        RC_fn3 = 3'b011,
        // unused  3'b100,
        RWI_fn3 = 3'b101,
        RSI_fn3 = 3'b110,
        RCI_fn3 = 3'b111
    } fn3_csr_t;

    typedef enum logic [1:0] {
        CSR_RW = 2'b01,
        CSR_RS = 2'b10,
        CSR_RC = 2'b11
    } csr_op_t;

    typedef enum logic [4:0] {
        BARE = 5'd0,
        SV32 = 5'd8
    } vm_t;

    localparam ASIDLEN = 9;//pid

    typedef enum logic [ECODE_W-1:0] {
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


    typedef enum logic [ECODE_W-1:0] {
        //RESERVED
        S_SOFTWARE_INTERRUPT = 5'd1,
        //ECODE_W
        M_SOFTWARE_INTERRUPT = 5'd3,
        //RESERVED
        S_TIMER_INTERRUPT = 5'd5,
        //RESERVED
        M_TIMER_INTERRUPT = 5'd7,
        //RESERVED
        S_EXTERNAL_INTERRUPT = 5'd9,
        //RESERVED
        M_EXTERNAL_INTERRUPT = 5'd11
    } interrupt_code_t;

    typedef enum bit [4:0] {
        AMO_LR_FN5 = 5'b00010,
        AMO_SC_FN5 = 5'b00011,
        AMO_SWAP_FN5 = 5'b00001,
        AMO_ADD_FN5 = 5'b00000,
        AMO_XOR_FN5 = 5'b00100,
        AMO_AND_FN5 = 5'b01100,
        AMO_OR_FN5 = 5'b01000,
        AMO_MIN_FN5 = 5'b10000,
        AMO_MAX_FN5 = 5'b10100,
        AMO_MINU_FN5 = 5'b11000,
        AMO_MAXU_FN5 = 5'b11100
    } amo_t;

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
