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

module csr_regs (
        input logic clk,
        input logic rst,

        //GC unit
        input csr_inputs_t csr_inputs,
        input new_request,
        input read_regs,
        input commit,
        input exception_packet_t gc_exception,
        output exception_packet_t csr_exception,
        output logic [1:0] current_privilege,

        //Decode
        input logic instruction_issued_no_rd,

        //exception_control
        input logic mret,
        input logic sret,

        //TLBs
        output logic tlb_on,
        output logic [ASIDLEN-1:0] asid,

        //MMUs
        mmu_interface.csr immu,
        mmu_interface.csr dmmu,

        //WB
        input logic instruction_complete,


        //External
        input logic interrupt,
        input logic timer_interrupt,

        output logic [XLEN-1:0] wb_csr,
        output logic [31:0] trap_pc,
        output logic [31:0] csr_mepc,
        output logic [31:0] csr_sepc
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
    (* ramstyle = "MLAB, no_rw_check" *) logic[XLEN-1:0] scratch_regs [31:0];//Only 0x1 and 0x3 used by supervisor and machine mode respectively
    logic[XLEN-1:0] scratch_out;


    logic[XLEN-1:0] mtvec;
    logic[XLEN-1:0] medeleg;
    logic[XLEN-1:0] mideleg;
    mip_t mip, mip_mask;
    mie_t mie_reg, mie_mask;

    logic[XLEN-1:0] mepc;

    logic[XLEN-1:0] mtimecmp;

    mcause_t mcause;
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

    satp_t satp;

    logic[COUNTER_W-1:0] mcycle;
    logic[COUNTER_W-1:0] mtime;
    logic[COUNTER_W-1:0] minst_ret;
    logic [1:0] inst_ret_inc;

    //write_logic
    logic supervisor_write;
    logic machine_write;

    //Control logic
    csr_addr_t csr_addr;
    logic privilege_exception;

    logic [XLEN-1:0] selected_csr;
    logic [XLEN-1:0] selected_csr_r;

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
    assign csr_addr = csr_inputs.csr_addr;
    assign privilege_exception = new_request & (csr_addr.privilege > privilege_level);

    assign supervisor_write = commit && !privilege_exception && (csr_addr.rw_bits != CSR_READ_ONLY && csr_addr.privilege == SUPERVISOR_PRIVILEGE);
    assign machine_write = commit && !privilege_exception && (csr_addr.rw_bits != CSR_READ_ONLY && csr_addr.privilege == MACHINE_PRIVILEGE);

    logic illegal_instruction;
    assign illegal_instruction = invalid_addr | privilege_exception;
    assign csr_exception.valid = new_request & illegal_instruction;

    assign machine_trap = gc_exception.valid && next_privilege_level == MACHINE_PRIVILEGE;
    assign supervisor_trap = gc_exception.valid && next_privilege_level == SUPERVISOR_PRIVILEGE;

    always_comb begin
        case (csr_inputs.csr_op)
            CSR_RW : updated_csr = csr_inputs.rs1;
            CSR_RS : updated_csr = selected_csr_r | csr_inputs.rs1;
            CSR_RC : updated_csr = selected_csr_r & ~csr_inputs.rs1;
            default : updated_csr = csr_inputs.rs1;
        endcase
    end

generate if (ENABLE_M_MODE) begin

    //Machine ISA register
    ////////////////////////////////////////////////////
    assign misa = '{default:0, base:1, A:1, S:1, M:1, I:1};


    //MSTATUS
    ////////////////////////////////////////////////////
    logic [1:0] trap_return_privilege_level, exception_privilege_level, interrupt_privilege_level;
    mstatus_t mstatus_exception, mstatus_return, mstatus_rst, mstatus_new;
    mstatus_t mstatus_mmask, mstatus_mask;
    logic exception_delegated;
    logic interrupt_delegated;

    assign exception_delegated = medeleg[gc_exception.code];
    assign interrupt_delegated = mideleg[gc_exception.code];

    assign trap_return_privilege_level = mret ? mstatus.mpp : {1'b0,mstatus.spp};
    assign exception_privilege_level = exception_delegated ? SUPERVISOR_PRIVILEGE : MACHINE_PRIVILEGE;
    assign interrupt_privilege_level = interrupt_delegated ? SUPERVISOR_PRIVILEGE : MACHINE_PRIVILEGE;

    always_comb begin
        if(mret | sret)
            next_privilege_level = trap_return_privilege_level;
        else if (interrupt)
            next_privilege_level = interrupt_privilege_level;
        else if (gc_exception.valid)
            next_privilege_level = exception_privilege_level;
        else
            next_privilege_level = privilege_level;
    end

    //Current privilege level
    always_ff @(posedge clk) begin
        if (rst)
            privilege_level <= MACHINE_PRIVILEGE;
        else
            privilege_level <= next_privilege_level;
    end
    assign current_privilege = privilege_level;

    always_comb begin
        mstatus_exception = mstatus;
        case (next_privilege_level)
            SUPERVISOR_PRIVILEGE: begin
                mstatus_exception.spie = (privilege_level == SUPERVISOR_PRIVILEGE) ? mstatus.sie : mstatus.uie;
                mstatus_exception.sie = 0;
                mstatus_exception.spp = privilege_level[0]; //one if from supervisor-mode, zero if from user-mode
            end
            default: begin
                mstatus_exception.mpie = (privilege_level == MACHINE_PRIVILEGE) ? mstatus.mie : ((privilege_level == SUPERVISOR_PRIVILEGE) ? mstatus.sie : mstatus.uie);
                mstatus_exception.mie = 0;
                mstatus_exception.mpp = privilege_level; //machine,supervisor or user
            end
        endcase
    end

    //return from trap
    always_comb begin
        mstatus_return = mstatus;
        if (sret) begin
            mstatus_return.sie = mstatus_return.spie;
            mstatus_return.spie = 1;
            mstatus_return.spp = 0;
        end else if (mret) begin
            mstatus_return.mie = mstatus.mpie;
            mstatus_return.mpie = 1;
            mstatus_return.mpp = USER_PRIVILEGE;
        end
    end

    assign mstatus_mmask = '{default:0, mprv:1, mxr:1, sum:1, mpp:'1, spp:1, mpie:1, spie:1, mie:1, sie:1};
    assign mstatus_smask  = '{default:0, mxr:1, sum:1, spp:1, spie:1, sie:1};
    assign mstatus_mask = mwrite_decoder[MSTATUS[5:0]] ? mstatus_mmask : mstatus_smask;

    always_comb begin
        if (mwrite_decoder[MSTATUS[5:0]] | swrite_decoder[SSTATUS[5:0]])
            mstatus_new = updated_csr & mstatus_mask;
        else if (interrupt | gc_exception.valid)
            mstatus_new = mstatus_exception;
        else if (mret | sret)
            mstatus_new = mstatus_return;
        else
            mstatus_new = mstatus;
    end

    assign mstatus_rst = '{default:0, mpp:MACHINE_PRIVILEGE};
    always_ff @(posedge clk) begin
        if (rst)
            mstatus <= mstatus_rst;
        else
            mstatus <= mstatus_new;
    end


    //MEDELEG
    ////////////////////////////////////////////////////
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

    //MEPC
    //Can be software written, written on exception with
    //exception causing PC.  Lower two bits tied to zero.
    ////////////////////////////////////////////////////
    always_ff @(posedge clk) begin
        mepc[1:0] <= '0;
        if (mwrite_decoder[MEPC[5:0]] | gc_exception.valid)
            mepc[XLEN-1:2] <= gc_exception.valid ? gc_exception.pc[XLEN-1:2] : updated_csr[XLEN-1:2];
    end
    assign csr_mepc = mepc;

    //MTVEC
    //No vectored mode, mode hard-coded to zero
    ////////////////////////////////////////////////////
    always_ff @(posedge clk) begin
        mtvec[1:0] <= '0;
        if (mwrite_decoder[MTVEC[5:0]])
            mtvec[XLEN-1:2] <= updated_csr[XLEN-1:2];
    end
    assign trap_pc = mtvec;

    //MCAUSE
    ////////////////////////////////////////////////////
    logic[XLEN-1:0] mcause_mask;
    always_ff @(posedge clk) begin
        mcause.zeroes <= '0;
        if (mwrite_decoder[MCAUSE[5:0]] | gc_exception.valid) begin
            mcause.interrupt <= gc_exception.valid ? 1'b0 :updated_csr[XLEN-1];
            mcause.code <= gc_exception.valid ? gc_exception.code : updated_csr[ECODE_W-1:0];
        end
    end

    //MTVAL
    ////////////////////////////////////////////////////
    always_ff @(posedge clk) begin
        if (mwrite_decoder[MTVAL[5:0]] | gc_exception.valid)
            mtval <=  gc_exception.valid ? gc_exception.tval : updated_csr;
    end

    //Scratch regs
    //For efficient LUT-RAM packing, all scratch regs are stored together
    ////////////////////////////////////////////////////
    logic scratch_reg_write;
    assign scratch_reg_write = mwrite_decoder[MSCRATCH[5:0]] | swrite_decoder[SSCRATCH[5:0]];

    always_ff @(posedge clk) begin
        if (scratch_reg_write)
            scratch_regs[{csr_addr.privilege, csr_addr.sub_addr[2:0]}] <= updated_csr;
    end
    assign scratch_out = scratch_regs[{csr_addr.privilege, csr_addr.sub_addr[2:0]}];

end
endgenerate

    ////////////////////////////////////////////////////
    //END OF MACHINE REGS
    ////////////////////////////////////////////////////












    ////////////////////////////////////////////////////
    //BEGIN OF SUPERVISOR REGS
    ////////////////////////////////////////////////////

generate if (ENABLE_M_MODE) begin

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

end
endgenerate

    ////////////////////////////////////////////////////
    //END OF SUPERVISOR REGS
    ////////////////////////////////////////////////////


    ////////////////////////////////////////////////////
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
            minst_ret <= 0;
        end else begin
            mcycle <= mcycle + 1;
            minst_ret <= minst_ret + COUNTER_W'(inst_ret_inc);
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
            MEPC : selected_csr = mepc;
            MCAUSE : selected_csr = mcause;
            MTVAL : selected_csr = mtval;
            MIP : selected_csr = mip;
            //Machine Timers and Counters
            MCYCLE : selected_csr = mcycle[XLEN-1:0];
            MINSTRET : selected_csr = minst_ret[XLEN-1:0];
            MCYCLEH : selected_csr = 32'(mcycle[COUNTER_W-1:XLEN]);
            MINSTRETH : selected_csr = 32'(minst_ret[COUNTER_W-1:XLEN]);

           //Supervisor Trap Setup
           SSTATUS : selected_csr = (mstatus & mstatus_smask);
           SEDELEG : selected_csr = 0; //No user-level interrupts/exception handling
           SIDELEG : selected_csr = 0;
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
            TIME : selected_csr = mcycle[XLEN-1:0];
            INSTRET : selected_csr = minst_ret[XLEN-1:0];
            CYCLEH : selected_csr = 32'(mcycle[COUNTER_W-1:XLEN]);
            TIMEH : selected_csr = 32'(mcycle[COUNTER_W-1:XLEN]);
            INSTRETH : selected_csr = 32'(minst_ret[COUNTER_W-1:XLEN]);

            default : begin selected_csr = 0; invalid_addr = 1; end
        endcase
    end

    always_ff @(posedge clk) begin
        if (read_regs)
            selected_csr_r <= selected_csr;
        else
            selected_csr_r <= 0;
    end

    assign wb_csr = selected_csr_r;

endmodule
