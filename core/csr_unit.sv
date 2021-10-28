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

module csr_regs

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;
    import csr_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        //Unit Interfaces
        input csr_inputs_t csr_inputs,
        input logic new_request,
        input id_t id,
        unit_writeback_interface.unit wb,

        input logic gc_issue_hold,
        input logic commit,

        input exception_packet_t gc_exception,
        output exception_packet_t csr_exception,
        output logic [1:0] current_privilege,
        input logic [31:0] exception_pc,

        //exception_control
        input logic mret,
        input logic sret,

        //TLBs
        output logic tlb_on,
        output logic [ASIDLEN-1:0] asid,

        //MMUs
        mmu_interface.csr immu,
        mmu_interface.csr dmmu,

        //Retire
        input retire_packet_t retire,

        //External
        input logic interrupt,
        input logic timer_interrupt,

        output logic [XLEN-1:0] wb_csr,
        output logic [31:0] trap_pc,
        output logic [31:0] csr_mepc,
        output logic [31:0] csr_sepc
        );

    //scratch ram
    (* ramstyle = "MLAB, no_rw_check" *) logic[XLEN-1:0] scratch_regs [31:0];//Only 0x1 and 0x3 used by supervisor and machine mode respectively
    logic[XLEN-1:0] scratch_out;

    csr_inputs_t csr_inputs_r;

    privilege_t privilege_level;
    privilege_t next_privilege_level;

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

    logic[CONFIG.CSRS.COUNTER_W-1:0] mcycle;
    logic[CONFIG.CSRS.COUNTER_W-1:0] mtime;
    logic[CONFIG.CSRS.COUNTER_W-1:0] minst_ret;
    localparam INST_RET_INC_W = 2;
    logic [INST_RET_INC_W-1:0] inst_ret_inc;

    //write_logic
    logic supervisor_write;
    logic machine_write;

    //Control logic
    logic privilege_exception;

    logic [XLEN-1:0] selected_csr;
    logic [XLEN-1:0] selected_csr_r;

    logic [31:0] updated_csr;

    logic invalid_addr;

    logic done;

    logic [255:0] swrite_decoder;
    logic [255:0] swrite_en;
    logic [255:0] mwrite_decoder;
    logic [255:0] mwrite_en;
    ////////////////////////////////////////////////////
    //Implementation
    always_ff @(posedge clk) begin
        if (new_request) begin
            csr_inputs_r <= csr_inputs;
        end
    end

    assign supervisor_write = commit && (csr_inputs_r.addr.rw_bits != CSR_READ_ONLY && csr_inputs_r.addr.privilege == SUPERVISOR_PRIVILEGE);
    assign machine_write = commit && (csr_inputs_r.addr.rw_bits != CSR_READ_ONLY && csr_inputs_r.addr.privilege == MACHINE_PRIVILEGE);

    always_comb begin
        swrite_decoder = 0;
        swrite_decoder[csr_inputs_r.addr.sub_addr] = supervisor_write ;
        mwrite_decoder = 0;
        mwrite_decoder[csr_inputs_r.addr.sub_addr] = machine_write ;
    end

    always_ff @(posedge clk) begin
        swrite_en <= swrite_decoder;
        mwrite_en <= mwrite_decoder;
    end

    ////////////////////////////////////////////////////
    //Exception Check
    assign privilege_exception = csr_inputs_r.addr.privilege > privilege_level;
    assign csr_exception.valid = commit & (invalid_addr | privilege_exception);

    always_comb begin
        case (csr_inputs_r.op)
            CSR_RW : updated_csr = csr_inputs_r.data;
            CSR_RS : updated_csr = selected_csr_r | csr_inputs_r.data;
            CSR_RC : updated_csr = selected_csr_r & ~csr_inputs_r.data;
            default : updated_csr = csr_inputs_r.data;
        endcase
    end

    ////////////////////////////////////////////////////
    //Machine Mode Registers
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Constant Registers

    ////////////////////////////////////////////////////
    //Machine ISA register
    const misa_t misa = '{default:0, mxlen:1, A:(CONFIG.INCLUDE_AMO), I:1, M:(CONFIG.INCLUDE_MUL && CONFIG.INCLUDE_DIV), S:(CONFIG.INCLUDE_S_MODE), U:(CONFIG.INCLUDE_U_MODE)};

    ////////////////////////////////////////////////////
    //Machine Version Registers
    const logic [XLEN-1:0] mvendorid = 0;
    const logic [XLEN-1:0] marchid = 0;
    const logic [XLEN-1:0] mimpid = CONFIG.CSRS.MACHINE_IMPLEMENTATION_ID;
    const logic [XLEN-1:0] mhartid = CONFIG.CSRS.CPU_ID;

    ////////////////////////////////////////////////////
    //MSTATUS
    const logic [XLEN-1:0] mstatush = 0; //Always little endian

    ////////////////////////////////////////////////////
    //Non-Constant Registers
    mstatus_t mstatus;

    logic[XLEN-1:0] mtvec;
    logic[XLEN-1:0] medeleg;
    logic[XLEN-1:0] mideleg;
    mip_t mip, mip_mask;
    mie_t mie_reg, mie_mask;

    logic[XLEN-1:0] mepc;

    logic[XLEN-1:0] mtimecmp;

    mcause_t mcause;
    logic[XLEN-1:0] mtval;

    //Virtualization support: TSR, TW, TVM unused
    //Extension context status: SD, FS, XS unused
    const mstatus_t mstatus_mask =
      '{default:0, mprv:(CONFIG.INCLUDE_U_MODE | CONFIG.INCLUDE_S_MODE), mxr:(CONFIG.INCLUDE_S_MODE),
      sum:(CONFIG.INCLUDE_U_MODE & CONFIG.INCLUDE_S_MODE), mpp:'1, spp:(CONFIG.INCLUDE_S_MODE),
      mpie:1, spie:(CONFIG.INCLUDE_S_MODE), mie:1, sie:(CONFIG.INCLUDE_S_MODE)};

    const mstatus_t sstatus_mask = '{default:0, mxr:1, sum:1, spp:1, spie:1, sie:1};


generate if (CONFIG.INCLUDE_M_MODE) begin

    privilege_t trap_return_privilege_level;
    privilege_t exception_privilege_level;
    privilege_t interrupt_privilege_level;

    mstatus_t mstatus_exception;
    mstatus_t mstatus_return;
    mstatus_t mstatus_new;

    //Interrupt and Exception Delegation
    //Can delegate to supervisor if currently in supervisor or user modes
    always_comb begin
        exception_privilege_level = MACHINE_PRIVILEGE;
        interrupt_privilege_level = MACHINE_PRIVILEGE;
        if (CONFIG.INCLUDE_S_MODE && privilege_level inside {SUPERVISOR_PRIVILEGE, USER_PRIVILEGE}) begin
            if (medeleg[gc_exception.code])
                exception_privilege_level = SUPERVISOR_PRIVILEGE;
            if (mideleg[gc_exception.code])
                interrupt_privilege_level = SUPERVISOR_PRIVILEGE;
        end
    end

    //return from trap privilege determination
    assign trap_return_privilege_level = mret ? privilege_t'(mstatus.mpp) : privilege_t'({1'b0,mstatus.spp});

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
                mstatus_exception.spie = (privilege_level == SUPERVISOR_PRIVILEGE) ? mstatus.sie : 0;
                mstatus_exception.sie = 0;
                mstatus_exception.spp = privilege_level[0]; //one if from supervisor-mode, zero if from user-mode
            end
            default: begin
                mstatus_exception.mpie = (privilege_level == MACHINE_PRIVILEGE) ? mstatus.mie : ((privilege_level == SUPERVISOR_PRIVILEGE) ? mstatus.sie : 0);
                mstatus_exception.mie = 0;
                mstatus_exception.mpp = privilege_level; //machine,supervisor or user
            end
        endcase
    end

    //return from trap
    always_comb begin
        mstatus_return = mstatus;
        if (sret) begin
            mstatus_return.sie = mstatus.spie;
            mstatus_return.spie = 1;
            mstatus_return.spp = USER_PRIVILEGE[0];
            mstatus_return.mprv = 0;
        end else if (mret) begin
            mstatus_return.mie = mstatus.mpie;
            mstatus_return.mpie = 1;
            mstatus_return.mpp = CONFIG.INCLUDE_U_MODE ? USER_PRIVILEGE : MACHINE_PRIVILEGE;
            if (mstatus.mpp != MACHINE_PRIVILEGE)
                mstatus_return.mprv = 0;
        end
    end

    mstatus_t mstatus_write_mask;
    assign mstatus_write_mask = mwrite_en[MSTATUS[7:0]] ? mstatus_mask : sstatus_mask;

    always_comb begin
        if (mwrite_en[MSTATUS[7:0]] | swrite_en[SSTATUS[7:0]])
            mstatus_new = (mstatus & ~mstatus_write_mask) | (updated_csr & mstatus_write_mask);
        else if (interrupt | gc_exception.valid)
            mstatus_new = mstatus_exception;
        else if (mret | sret)
            mstatus_new = mstatus_return;
        else
            mstatus_new = mstatus;
    end

    always_ff @(posedge clk) begin
        if (rst)
            mstatus <= '{default:0, mpp:MACHINE_PRIVILEGE};
        else
            mstatus <= mstatus_new;
    end

    ////////////////////////////////////////////////////
    //MTVEC
    //No vectored mode, mode hard-coded to zero
    always_ff @(posedge clk) begin
        mtvec[1:0] <= '0;
        if (mwrite_en[MTVEC[7:0]])
            mtvec[XLEN-1:2] <= updated_csr[XLEN-1:2];
    end
    assign trap_pc = mtvec;

    ////////////////////////////////////////////////////
    //MEDELEG
    logic [31:0] medeleg_mask;
    always_comb begin
        medeleg_mask = 0;
        if (CONFIG.INCLUDE_S_MODE) begin
            medeleg_mask[INST_ADDR_MISSALIGNED] = 1;
            medeleg_mask[INST_ACCESS_FAULT] = 1;
            medeleg_mask[ILLEGAL_INST] = 1;
            medeleg_mask[BREAK] = 1;
            medeleg_mask[LOAD_ADDR_MISSALIGNED] = 1;
            medeleg_mask[LOAD_FAULT] = 1;
            medeleg_mask[STORE_AMO_ADDR_MISSALIGNED] = 1;
            medeleg_mask[STORE_AMO_FAULT] = 1;
            medeleg_mask[ECALL_U] = 1;
            medeleg_mask[INST_PAGE_FAULT] = 1;
            medeleg_mask[LOAD_PAGE_FAULT] = 1;
            medeleg_mask[STORE_OR_AMO_PAGE_FAULT] = 1;
        end
    end

    always_ff @(posedge clk) begin
        if (rst)
            medeleg <= '0;
        else if (mwrite_en[MEDELEG[7:0]])
            medeleg <= (updated_csr & medeleg_mask);
    end

    ////////////////////////////////////////////////////
    //MIDELEG
    logic [31:0] mideleg_mask;
    always_comb begin
        mideleg_mask = 0;
        if (CONFIG.INCLUDE_S_MODE) begin
            mideleg_mask[S_SOFTWARE_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
            mideleg_mask[S_TIMER_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
            mideleg_mask[S_EXTERNAL_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
        end
    end
    always_ff @(posedge clk) begin
        if (rst)
            mideleg <= '0;
        else if (mwrite_en[MIDELEG[7:0]])
            mideleg <= (updated_csr & mideleg_mask);
    end

    ////////////////////////////////////////////////////
    //MIP
    assign mip_mask = '{default:0, meip:1, seip:CONFIG.INCLUDE_S_MODE, mtip:1, stip:CONFIG.INCLUDE_S_MODE, msip:1, ssip:CONFIG.INCLUDE_S_MODE};
    always_ff @(posedge clk) begin
        if (rst)
            mip <= 0;
        else if (mwrite_en[MIP[7:0]])
            mip <= (updated_csr & mip_mask);
    end

    ////////////////////////////////////////////////////
    //MIE
    assign mie_mask = '{default:0, meie:1, seie:CONFIG.INCLUDE_S_MODE, mtie:1, stie:CONFIG.INCLUDE_S_MODE, msie:1, ssie:CONFIG.INCLUDE_S_MODE};
    assign sie_mask = '{default:0, seie:1, stie:1, ssie:1};

    always_ff @(posedge clk) begin
        if (rst)
            mie_reg <= '0;
        else if (mwrite_en[MIE[7:0]])
            mie_reg <= (updated_csr & mie_mask);
        else if (swrite_en[SIE[7:0]])
            mie_reg <= (updated_csr & sie_mask);
    end

    ////////////////////////////////////////////////////
    //MEPC
    //Can be software written, written on exception with
    //exception causing PC.  Lower two bits tied to zero.
    always_ff @(posedge clk) begin
        mepc[1:0] <= '0;
        if (mwrite_en[MEPC[7:0]] | gc_exception.valid)
            mepc[XLEN-1:2] <= gc_exception.valid ? exception_pc[XLEN-1:2] : updated_csr[XLEN-1:2];
    end
    assign csr_mepc = mepc;


    ////////////////////////////////////////////////////
    //MCAUSE
    //As the exception and interrupts codes are sparsely populated,
    //to ensure that only legal values are written, a ROM lookup
    //is used to validate the CSR write operation
    logic MCAINCLUDE_EXCEPTION_MASKING_ROM [2**ECODE_W];
    logic MCAINCLUDE_INTERRUPT_MASKING_ROM [2**ECODE_W];
    always_comb begin
        MCAINCLUDE_EXCEPTION_MASKING_ROM = '{default: 0};
        MCAINCLUDE_EXCEPTION_MASKING_ROM[INST_ADDR_MISSALIGNED] = 1;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[INST_ACCESS_FAULT] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[ILLEGAL_INST] = 1;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[BREAK] = 1;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[LOAD_ADDR_MISSALIGNED] = 1;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[LOAD_FAULT] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[STORE_AMO_ADDR_MISSALIGNED] = 1;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[STORE_AMO_FAULT] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[ECALL_U] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[ECALL_S] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[ECALL_M] = 1;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[INST_PAGE_FAULT] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[LOAD_PAGE_FAULT] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_EXCEPTION_MASKING_ROM[STORE_OR_AMO_PAGE_FAULT] = CONFIG.INCLUDE_S_MODE;

        MCAINCLUDE_INTERRUPT_MASKING_ROM = '{default: 0};
        MCAINCLUDE_INTERRUPT_MASKING_ROM[S_SOFTWARE_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_INTERRUPT_MASKING_ROM[M_SOFTWARE_INTERRUPT] = 1;
        MCAINCLUDE_INTERRUPT_MASKING_ROM[S_TIMER_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_INTERRUPT_MASKING_ROM[M_TIMER_INTERRUPT] = 1;
        MCAINCLUDE_INTERRUPT_MASKING_ROM[S_EXTERNAL_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
        MCAINCLUDE_INTERRUPT_MASKING_ROM[M_EXTERNAL_INTERRUPT] = 1;
    end

    logic mcause_write_valid;
    always_comb begin
        if (updated_csr[XLEN-1]) //interrupt
            mcause_write_valid = MCAINCLUDE_INTERRUPT_MASKING_ROM[updated_csr[ECODE_W-1:0]];
        else
            mcause_write_valid = MCAINCLUDE_EXCEPTION_MASKING_ROM[updated_csr[ECODE_W-1:0]];
    end

    always_ff @(posedge clk) begin
        mcause.zeroes <= '0;
        if ((mcause_write_valid & mwrite_en[MCAUSE[7:0]]) | gc_exception.valid) begin
            mcause.interrupt <= gc_exception.valid ? 1'b0 : updated_csr[XLEN-1];
            mcause.code <= gc_exception.valid ? gc_exception.code : updated_csr[ECODE_W-1:0];
        end
    end

    ////////////////////////////////////////////////////
    //MTVAL
    always_ff @(posedge clk) begin
        if (mwrite_en[MTVAL[7:0]] | gc_exception.valid)
            mtval <=  gc_exception.valid ? gc_exception.tval : updated_csr;
    end

    ////////////////////////////////////////////////////
    //Scratch regs
    //For efficient LUT-RAM packing, all scratch regs are stored together
    logic scratch_reg_write;
    assign scratch_reg_write = mwrite_en[MSCRATCH[7:0]] | swrite_en[SSCRATCH[7:0]];

    always_ff @(posedge clk) begin
        if (scratch_reg_write)
            scratch_regs[{csr_inputs_r.addr.privilege, csr_inputs_r.addr.sub_addr[2:0]}] <= updated_csr;
    end
    assign scratch_out = scratch_regs[{csr_inputs_r.addr.privilege, csr_inputs_r.addr.sub_addr[2:0]}];

end
endgenerate

    ////////////////////////////////////////////////////
    //END OF MACHINE REGS
    ////////////////////////////////////////////////////












    ////////////////////////////////////////////////////
    //BEGIN OF SUPERVISOR REGS
    ////////////////////////////////////////////////////
    //TLB status --- used to mux physical/virtual address
    assign tlb_on = CONFIG.INCLUDE_S_MODE & satp.mode;
    assign asid = satp.asid;
    //******************

generate if (CONFIG.INCLUDE_S_MODE) begin
    ////////////////////////////////////////////////////
    //MMU interface
    assign immu.mxr = mstatus.mxr;
    assign dmmu.mxr = mstatus.mxr;
    assign immu.sum = mstatus.sum;
    assign dmmu.sum = mstatus.sum;
    assign immu.privilege = privilege_level;
    assign dmmu.privilege = mstatus.mprv ? mstatus.mpp : privilege_level;
    assign immu.satp_ppn = satp.ppn;
    assign dmmu.satp_ppn = satp.ppn;
    ////////////////////////////////////////////////////

    assign sip_mask =  '{default:0, seip:1, stip:1, ssip:1};

    ////////////////////////////////////////////////////
    //STVEC
    logic [31:0] stvec_mask = '1;
    always_ff @(posedge clk) begin
        if (rst)
            stvec <= {CONFIG.CSRS.RESET_VEC[XLEN-1:2], 2'b00};
        else if (swrite_en[STVEC[7:0]])
            stvec <= (updated_csr & stvec_mask);
    end

    ////////////////////////////////////////////////////
    //SATP
    logic[XLEN-1:0] satp_mask;
    assign satp_mask = '1;
    always_ff @(posedge clk) begin
        if (rst)
            satp <= 0;
        else if (swrite_en[SATP[7:0]])
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
    //Increments suppressed on writes to these registers
    logic[CONFIG.CSRS.COUNTER_W-1:0] mcycle_input_next;
    logic mcycle_inc;

    assign mcycle_input_next[31:0] = mwrite_en[MCYCLE[7:0]] ? updated_csr : mcycle[31:0];
    assign mcycle_input_next[CONFIG.CSRS.COUNTER_W-1:32] = mwrite_en[MCYCLEH[7:0]] ? updated_csr[CONFIG.CSRS.COUNTER_W-33:0] : mcycle[CONFIG.CSRS.COUNTER_W-1:32];

    assign mcycle_inc = ~(mwrite_en[MCYCLE[7:0]] | mwrite_en[MCYCLEH[7:0]]);

    always_ff @(posedge clk) begin
        if (rst) 
            mcycle <= 0;
        else
            mcycle <= mcycle_input_next + CONFIG.CSRS.COUNTER_W'(mcycle_inc);
    end

    logic[CONFIG.CSRS.COUNTER_W-1:0] minst_ret_input_next;
    logic[LOG2_RETIRE_PORTS:0] minst_ret_inc;
    assign minst_ret_input_next[31:0] = mwrite_en[MINSTRET[7:0]] ? updated_csr : minst_ret[31:0];
    assign minst_ret_input_next[CONFIG.CSRS.COUNTER_W-1:32] = mwrite_en[MINSTRETH[7:0]] ? updated_csr[CONFIG.CSRS.COUNTER_W-33:0] : minst_ret[CONFIG.CSRS.COUNTER_W-1:32];

    assign minst_ret_inc = {(LOG2_RETIRE_PORTS+1){~(mwrite_en[MINSTRET[7:0]] | mwrite_en[MINSTRETH[7:0]])}} & retire.count;

    always_ff @(posedge clk) begin
        if (rst)
            minst_ret <= 0;
        else
            minst_ret <= minst_ret_input_next + CONFIG.CSRS.COUNTER_W'(minst_ret_inc);
    end


    ////////////////////////////////////////////////////
    //CSR mux
    always_comb begin
        invalid_addr = 0;
        case (csr_inputs_r.addr) inside
            //Machine info
            MISA :  selected_csr = CONFIG.INCLUDE_M_MODE ? misa : 0;
            MVENDORID : selected_csr = CONFIG.INCLUDE_M_MODE ? mvendorid : 0;
            MARCHID : selected_csr = CONFIG.INCLUDE_M_MODE ? marchid : 0;
            MIMPID : selected_csr = CONFIG.INCLUDE_M_MODE ? mimpid : 0;
            MHARTID : selected_csr = CONFIG.INCLUDE_M_MODE ? mhartid : 0;
            //Machine trap setup
            MSTATUS : selected_csr = CONFIG.INCLUDE_M_MODE ? mstatus : 0;
            MEDELEG : selected_csr = CONFIG.INCLUDE_M_MODE ? medeleg : 0;
            MIDELEG : selected_csr = CONFIG.INCLUDE_M_MODE ? mideleg : 0;
            MIE : selected_csr = CONFIG.INCLUDE_M_MODE ? mie_reg : 0;
            MTVEC : selected_csr = CONFIG.INCLUDE_M_MODE ? mtvec : 0;
            MCOUNTEREN : selected_csr = 0;
            //Machine trap handling
            MSCRATCH : selected_csr = CONFIG.INCLUDE_M_MODE ? scratch_out : 0;
            MEPC : selected_csr = CONFIG.INCLUDE_M_MODE ? mepc : 0;
            MCAUSE : selected_csr = CONFIG.INCLUDE_M_MODE ? mcause : 0;
            MTVAL : selected_csr = CONFIG.INCLUDE_M_MODE ? mtval : 0;
            MIP : selected_csr = CONFIG.INCLUDE_M_MODE ? mip : 0;
            //Machine Memory Protection
            [12'h3EF : 12'h3A0] : selected_csr = 0;
            //Machine Timers and Counters
            MCYCLE : selected_csr = CONFIG.INCLUDE_M_MODE ? mcycle[XLEN-1:0] : 0;
            MINSTRET : selected_csr = CONFIG.INCLUDE_M_MODE ? minst_ret[XLEN-1:0] : 0;
            [12'hB03 : 12'hB1F] : selected_csr = 0;
            MCYCLEH : selected_csr = CONFIG.INCLUDE_M_MODE ? 32'(mcycle[CONFIG.CSRS.COUNTER_W-1:XLEN]) : 0;
            MINSTRETH : selected_csr = CONFIG.INCLUDE_M_MODE ? 32'(minst_ret[CONFIG.CSRS.COUNTER_W-1:XLEN]) : 0;
            [12'hB83 : 12'hB9F] : selected_csr = 0;
            //Machine Counter Setup
            [12'h320 : 12'h33F] : selected_csr = 0;

            //Supervisor Trap Setup
            SSTATUS : selected_csr = CONFIG.INCLUDE_S_MODE ? (mstatus & sstatus_mask) : '0;
            SEDELEG : selected_csr = 0; //No user-level interrupts/exception handling
            SIDELEG : selected_csr = 0;
            SIE : selected_csr = CONFIG.INCLUDE_S_MODE ? (mie_reg & sie_mask) : '0;
            STVEC : selected_csr = CONFIG.INCLUDE_S_MODE ? stvec : '0;
            SCOUNTEREN : selected_csr = 0;
            //Supervisor trap handling
            SSCRATCH : selected_csr = CONFIG.INCLUDE_S_MODE ? scratch_out : '0;
            SEPC : selected_csr = CONFIG.INCLUDE_S_MODE ? scratch_out : '0;
            SCAUSE : selected_csr = CONFIG.INCLUDE_S_MODE ? scratch_out : '0;
            STVAL : selected_csr = CONFIG.INCLUDE_S_MODE ? scratch_out : '0;
            SIP : selected_csr = CONFIG.INCLUDE_S_MODE ? (mip & sip_mask) : '0;
            //Supervisor Protection and Translation
            SATP : selected_csr = CONFIG.INCLUDE_S_MODE ? satp : '0;

            //User status
            //Floating point
            FFLAGS : selected_csr = 0;
            FRM : selected_csr = 0;
            FCSR : selected_csr = 0;
            //User Counter Timers
            CYCLE : selected_csr = mcycle[XLEN-1:0];
            TIME : selected_csr = mcycle[XLEN-1:0];
            INSTRET : selected_csr = minst_ret[XLEN-1:0];
            [12'hC03 : 12'hC1F] : selected_csr = 0;
            CYCLEH : selected_csr = 32'(mcycle[CONFIG.CSRS.COUNTER_W-1:XLEN]);
            TIMEH : selected_csr = 32'(mcycle[CONFIG.CSRS.COUNTER_W-1:XLEN]);
            INSTRETH : selected_csr = 32'(minst_ret[CONFIG.CSRS.COUNTER_W-1:XLEN]);
            [12'hC83 : 12'hC9F] : selected_csr = 0;

            default : begin selected_csr = 0; invalid_addr = 1; end
        endcase
    end
    always_ff @(posedge clk) begin
        if (commit)
            selected_csr_r <= selected_csr;
    end

    ////////////////////////////////////////////////////
    //Output
    always_ff @(posedge clk) begin
        if (new_request)
            wb.id <=  id;
    end

    always_ff @(posedge clk) begin
        if (rst)
            wb.done <= 0;
        else
            wb.done <= commit;
    end

    assign wb.rd = selected_csr_r;

endmodule
