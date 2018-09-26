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

import taiga_config::*;
import taiga_types::*;
import csr_types::*;

module csr_unit (
        input logic clk,
        input logic rst,
        func_unit_ex_interface.unit csr_ex,
        unit_writeback_interface.unit csr_wb, //        writeback_unit_interface_dummy.unit csr_wb, //        writeback_unit_interface_dummy.unit csr_wb,

        //Decode
        input csr_inputs_t csr_inputs,
        input logic instruction_issued_no_rd,

        //exception_control
        exception_interface.unit csr_exception,
        csr_exception_interface.csr gc_exception,
        input logic mret,
        input logic sret,

        //TLBs
        output logic tlb_on,
        output logic [6:0] asid,

        //MMUs
        mmu_interface.csr immu,
        mmu_interface.csr dmmu,

        //WB
        input logic instruction_complete,

        input logic return_from_exception,

        //External
        input logic interrupt,
        input logic timer_interrupt

        );

    misa_t misa;

    bit [XLEN-1:0] mvendorid = 0;
    bit [XLEN-1:0] marchid = 0;
    bit [XLEN-1:0] mimpid = 0;
    bit [XLEN-1:0] mhartid = CPU_ID;


    //Non-constant registers
    mstatus_t mstatus;
    mstatus_t mstatus_smask;
    logic [1:0] privilege_level, next_privilege_level;

    //scratch ram
    logic[XLEN-1:0] scratch_regs [31:0];//Only 0x1 and 0x3 used by supervisor and machine mode respectively
    logic[XLEN-1:0] scratch_out;


    logic[XLEN-1:0] mtvec;
    logic[XLEN-1:0] medeleg;
    logic[XLEN-1:0] mideleg;
    mip_t mip, mip_mask;
    mie_t mie_reg, mie_mask;
    logic[XLEN-1:0] mepc;

    logic[XLEN-1:0] mtimecmp;

    logic[XLEN-1:0] mcause;
    logic[XLEN-1:0] mtval;

    mip_t sip_mask;
    mie_t sie_mask;
    logic[XLEN-1:0] sepc;

    logic[XLEN-1:0] stime;
    logic[XLEN-1:0] stimecmp;

    logic[XLEN-1:0] scause;
    logic[XLEN-1:0] stval;

    logic[XLEN-1:0] sstatus;
    logic[XLEN-1:0] stvec;

    logic[TIMER_W-1:0] mcycle;
    logic[TIMER_W-1:0] mtime;
    logic[TIMER_W-1:0] minst_ret;
    logic [1:0] inst_ret_inc;

    //write_logic
    logic user_write;
    logic supervisor_write;
    logic machine_write;

    //Control logic
    csr_addr_t csr_addr;
    logic privilege_exception;



    logic [31:0] selected_csr;
    logic [31:0] updated_csr;

    logic invalid_addr;

    logic machine_trap;
    logic supervisor_trap;

    logic done;

    logic [63:0] swrite_decoder;
    logic [63:0] mwrite_decoder;

    //******************************************************************
    //TLB status --- used to mux physical/virtual address
    assign tlb_on = satp.mode;
    assign asid = satp.asid;
    //******************

    //MMU interface
    assign immu.mxr = mstatus.mxr;
    assign dmmu.mxr = mstatus.mxr;
    assign immu.pum = mstatus.sum;
    assign dmmu.pum = mstatus.sum;
    assign immu.privilege = privilege_level;
    assign dmmu.privilege = mstatus.mprv ? mstatus.mpp : privilege_level;
    assign immu.ppn = satp.ppn;
    assign dmmu.ppn = satp.ppn;
    //******************


    always_comb begin
        swrite_decoder = 0;
        swrite_decoder[csr_addr.sub_addr] = supervisor_write ;
        mwrite_decoder = 0;
        mwrite_decoder[csr_addr.sub_addr] = machine_write ;
    end

    //convert addr into packed struct form
    assign  csr_addr = csr_inputs.csr_addr;
    assign privilege_exception = csr_ex.new_request  && (csr_addr.privilege > privilege_level);

    assign user_write = !privilege_exception && (csr_addr.rw_bits != CSR_READ_ONLY && csr_addr.privilege == USER_PRIV);
    assign supervisor_write = !privilege_exception && (csr_addr.rw_bits != CSR_READ_ONLY && csr_addr.privilege == SUPERVISOR_PRIV);
    assign machine_write = !privilege_exception && (csr_addr.rw_bits != CSR_READ_ONLY && csr_addr.privilege == MACHINE_PRIV);

    assign gc_exception.illegal_instruction = invalid_addr | privilege_exception;

    assign machine_trap = gc_exception.valid && next_privilege_level == MACHINE_PRIV;
    assign supervisor_trap = gc_exception.valid && next_privilege_level == SUPERVISOR_PRIV;

    always_comb begin
        case (csr_inputs.csr_op)
            //  CSR_RW : updated_csr = csr_inputs.rs1;
            CSR_RS : updated_csr = selected_csr | csr_inputs.rs1;
            CSR_RC : updated_csr = selected_csr & ~csr_inputs.rs1;
            default : updated_csr = csr_inputs.rs1;//selected_csr;
        endcase
    end

    //Machine ISA register
    assign misa = '{default:0, base:1, A:1, S:1, M:1, I:1};
    //assign misa = '{default:0, base:1, A:0, S:1, M:1, I:1};
    //assign misa = '{default:0, base:1, A:0, S:1, M:0, I:1};

    //mstatus and privilege
    mstatus_priv_reg mstatus_and_privilege_regs (.*, .exception(gc_exception.valid),
            .interrupt_delegated(mideleg[gc_exception.code]), .exception_delegated(medeleg[gc_exception.code]),
            .write_msr_m(mwrite_decoder[MSTATUS[5:0]]),.write_msr_s(swrite_decoder[SSTATUS[5:0]])
            );

    //medeleg
    logic [31:0] medeleg_mask;
    always_comb begin
        medeleg_mask = 0;
        medeleg_mask[INST_ADDR_MISSALIGNED] = 1;
        medeleg_mask[INST_ACCESS_FAULT] = 1;
        medeleg_mask[ILLEGAL_INST] = 1;
        medeleg_mask[BREAK] = 1;//?
        medeleg_mask[LOAD_FAULT] = 1;
        medeleg_mask[STORE_AMO_FAULT] = 1;
        medeleg_mask[ECALL_U] = 1;
        medeleg_mask[INST_PAGE_FAULT] = 1;
        medeleg_mask[LOAD_PAGE_FAULT] = 1;
        medeleg_mask[STORE_OR_AMO_PAGE_FAULT] = 1;
    end
    always_ff @(posedge clk) begin
        if (rst)
            medeleg <= '0;
        else if (mwrite_decoder[MEDELEG[5:0]])
            medeleg <= (updated_csr & medeleg_mask);
    end

    //mideleg
    logic [31:0] mideleg_mask;
    always_comb begin
        mideleg_mask = 0;
        mideleg_mask[S_SOFTWARE_INTERRUPT] = 1;
        mideleg_mask[S_TIMER_INTERRUPT] = 1;
        mideleg_mask[S_EXTERNAL_INTERRUPT] = 1;
    end
    always_ff @(posedge clk) begin
        if (rst)
            mideleg <= '0;
        else if (mwrite_decoder[MIDELEG[5:0]])
            mideleg <= (updated_csr & mideleg_mask);
    end

    //mip
    assign mip_mask = '{default:0, stip:1, ssip:1};
    always_ff @(posedge clk) begin
        if (rst)
            mip <= 0;
        else if (mwrite_decoder[MIP[5:0]])
            mip <= (updated_csr & mip_mask);
    end

    //mie
    assign mie_mask = '{default:0, meie:1, seie:1, mtie:1, stie:1, msie:1, ssie:1};
    assign sie_mask = '{default:0, seie:1, stie:1, ssie:1};

    always_ff @(posedge clk) begin
        if (rst)
            mie_reg <= '0;
        else if (mwrite_decoder[MIE[5:0]])
            mie_reg <= (updated_csr & mie_mask);
        else if (swrite_decoder[SIE[5:0]])
            mie_reg <= (updated_csr & sie_mask);
    end


    //mtvec
    logic [31:0] mtvec_mask = '1;
    always_ff @(posedge clk) begin
        if (rst)
            mtvec <= {RESET_VEC[XLEN-1:2], 2'b00};
        else if (mwrite_decoder[MTVEC[5:0]])
            mtvec <= (updated_csr & mtvec_mask);
    end

    //mepc
    logic [31:0] mepc_mask;
    assign mepc_mask = {30'b1, 2'b0};
    //mcause
    logic [31:0] mcause_mask;
    always_comb begin
        mcause_mask = 0;
        mcause_mask[31] = 1;
        mcause_mask[ECODE_W-1:0] = '1;
    end
    //scratch regs
    logic [31:0] scratch_mask;
    assign scratch_mask = '1;

    logic [31:0] lut_reg_mask;
    always_comb begin
        if (csr_addr.sub_addr[2:0] == MEPC[2:0])
            lut_reg_mask = mepc_mask;
        else if (csr_addr.sub_addr[2:0] == MCAUSE[2:0])
            lut_reg_mask = mcause_mask;
        else
            lut_reg_mask = '1;
    end

    always_ff @(posedge clk) begin
        if (mwrite_decoder[MSCRATCH[5:0]] | mwrite_decoder[MEPC[5:0]] | mwrite_decoder[MCAUSE[5:0]] | mwrite_decoder[MTVAL[5:0]] |
                swrite_decoder[SSCRATCH[5:0]] | swrite_decoder[SEPC[5:0]] | swrite_decoder[SCAUSE[5:0]] | swrite_decoder[STVAL[5:0]]
            )
            scratch_regs[{csr_addr.privilege, csr_addr.sub_addr[2:0]}] <= (updated_csr & lut_reg_mask);
    end
    assign scratch_out = scratch_regs[{csr_addr.privilege, csr_addr.sub_addr[2:0]}];



    //END OF MACHINE REGS



    //BEGIN OF SUPERVISOR REGS

    assign sip_mask =  '{default:0, seip:1, stip:1, ssip:1};

    //stvec
    logic [31:0] stvec_mask = '1;
    always_ff @(posedge clk) begin
        if (rst)
            stvec <= {RESET_VEC[XLEN-1:2], 2'b00};
        else if (swrite_decoder[STVEC[5:0]])
            stvec <= (updated_csr & stvec_mask);
    end

    //satp
    logic[XLEN-1:0] satp_mask;
    assign satp_mask = '1;
    always_ff @(posedge clk) begin
        if (rst)
            satp <= 0;
        else if (swrite_decoder[SATP[5:0]])
            satp <= (updated_csr & satp_mask);
    end

    //Timers and Counters

    //Register increment for instructions completed
    always_ff @(posedge clk) begin
        if (rst) begin
            inst_ret_inc <= 0;
        end else begin
            if (instruction_complete & instruction_issued_no_rd)
                inst_ret_inc <= 2;
            else if (instruction_complete | instruction_issued_no_rd)
                inst_ret_inc <= 1;
            else
                inst_ret_inc <= 0;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            mcycle <= 0;
            mtime <= 0;
            minst_ret <= 0;
        end else begin
            mcycle <= mcycle + 1;
            mtime <= mtime + 1;
            minst_ret <= minst_ret + inst_ret_inc;
        end
    end


    always_comb begin
        invalid_addr = 0;
        case(csr_addr)
            //Machine info
            MISA :  selected_csr = misa;
            MVENDORID : selected_csr = mvendorid;
            MARCHID : selected_csr = marchid;
            MIMPID : selected_csr = mimpid;
            MHARTID : selected_csr = mhartid;
                //Machine trap setup
            MSTATUS : selected_csr = mstatus;
            MEDELEG : selected_csr = medeleg;
            MIDELEG : selected_csr = mideleg;
            MIE : selected_csr = mie_reg;
            MTVEC : selected_csr = mtvec;
                //Machine trap handling
            MSCRATCH : selected_csr = scratch_out;
            MEPC : selected_csr = scratch_out;
            MCAUSE : selected_csr = scratch_out;
            MTVAL : selected_csr = scratch_out;
            MIP : selected_csr = mip;
                //Machine Timers and Counters
            MCYCLE : selected_csr = mcycle[XLEN-1:0];
            MINSTRET : selected_csr = minst_ret[XLEN-1:0];
            MCYCLEH : selected_csr = mcycle[TIMER_W-1:XLEN];
            MINSTRETH : selected_csr = minst_ret[TIMER_W-1:XLEN];

                //Supervisor Trap Setup
            SSTATUS : selected_csr = (mstatus & mstatus_smask);
            //SEDELEG : selected_csr = 0; //No user-level interrupts/exception handling
            //SIDELEG : selected_csr = 0;
            SIE : selected_csr = (mie_reg & sie_mask);
            STVEC : selected_csr = stvec;
                //Supervisor trap handling
            SSCRATCH : selected_csr = scratch_out;
            SEPC : selected_csr = scratch_out;
            SCAUSE : selected_csr = scratch_out;
            STVAL : selected_csr = scratch_out;
            SIP : selected_csr = (mip & sip_mask);
                //Supervisor Protection and Translation
            SATP : selected_csr = satp;
                //User status
                //Floating point
                //User Counter Timers
            CYCLE : selected_csr = mcycle[XLEN-1:0];
            TIME : selected_csr = mtime[XLEN-1:0];
            INSTRET : selected_csr = minst_ret[XLEN-1:0];
            CYCLEH : selected_csr = mcycle[TIMER_W-1:XLEN];
            TIMEH : selected_csr = mtime[TIMER_W-1:XLEN];
            INSTRETH : selected_csr = minst_ret[TIMER_W-1:XLEN];

            default : begin selected_csr = 0; invalid_addr = 1; end
        endcase
    end


    always_ff @(posedge clk) begin
        if (rst) begin
            csr_ex.ready <= 1;
        end else if (csr_ex.new_request_dec) begin
            csr_ex.ready <= 0;
        end else if (csr_wb.accepted) begin
            csr_ex.ready <= 1;
        end
    end

    always_ff @(posedge clk) begin
        if (csr_ex.new_request) begin
            csr_wb.rd <= selected_csr;
        end
    end

    assign csr_wb.done_next_cycle = 1;//if in queue, will be done on next cycle, no-pipelining
    assign csr_wb.done_on_first_cycle = 0;//registered output, done after one cycle

    always_ff @(posedge clk) begin
        if (rst) begin
            done <= 0;
        end else if (csr_ex.new_request) begin
            done <= 1;
        end else if (csr_wb.accepted) begin
            done <= 0;
        end
    end


endmodule
