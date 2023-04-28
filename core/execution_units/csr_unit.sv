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

module csr_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import csr_types::*;
    import opcodes::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        input decode_packet_t decode_stage,
        output logic unit_needed,
        output logic [REGFILE_READ_PORTS-1:0] uses_rs,
        output logic uses_rd,

        input issue_packet_t issue_stage,
        input logic issue_stage_ready,
        input rs_addr_t issue_rs_addr [REGFILE_READ_PORTS],
        input logic [31:0] rf [REGFILE_READ_PORTS],

        //Unit Interfaces
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb,

        //Privilege
        output logic [1:0] current_privilege,

        //GC
        input logic interrupt_taken,
        output logic interrupt_pending,
        output logic processing_csr,

        //TLB and MMU
        output logic tlb_on,
        output logic [ASIDLEN-1:0] asid,

        //MMUs
        mmu_interface.csr immu,
        mmu_interface.csr dmmu,

        //CSR exception interface
        input exception_packet_t exception,
        output logic [31:0] exception_target_pc,

        //exception return
        input logic mret,
        input logic sret,
        output logic [31:0] epc,

        //Retire
        input retire_packet_t wb_retire,
        input id_t retire_ids [RETIRE_PORTS],
        input logic [LOG2_RETIRE_PORTS : 0] retire_count,

        //External
        input interrupt_t s_interrupt,
        input interrupt_t m_interrupt
        );

    typedef struct packed{
        csr_addr_t addr;
        logic[1:0] op;
        logic reads;
        logic writes;
        logic [31:0] data;
    } csr_inputs_t;

    typedef enum logic [2:0] {
        MSTATUS_UNCHANGED = 0,
        MSTATUS_WRITE = 1,
        MSTATUS_INTERRUPT = 2,
        MSTATUS_EXCEPTION = 3,
        MSTATUS_MRET = 4,
        MSTATUS_SRET = 5
    } mstatus_cases_t;
    mstatus_cases_t mstatus_case;

    logic busy;
    logic commit;
    logic commit_in_progress;

    csr_inputs_t csr_inputs;
    csr_inputs_t csr_inputs_r;

    privilege_t privilege_level;
    privilege_t next_privilege_level;

    //write_logic
    logic swrite;
    logic mwrite;
    logic [255:0] sub_write_en;

    logic [31:0] selected_csr;
    logic [31:0] selected_csr_r;

    logic [31:0] updated_csr;

    function logic mwrite_en (input csr_addr_t addr);
        return mwrite & sub_write_en[addr.sub_addr];
    endfunction
    function logic swrite_en (input csr_addr_t addr);
        return swrite & sub_write_en[addr.sub_addr];
    endfunction

    ////////////////////////////////////////////////////
    //Legalization Functions
    function logic [31:0] init_medeleg_mask();
       init_medeleg_mask = 0;
        if (CONFIG.INCLUDE_S_MODE) begin
            init_medeleg_mask[INST_ADDR_MISSALIGNED] = 1;
            init_medeleg_mask[INST_ACCESS_FAULT] = 1;
            init_medeleg_mask[ILLEGAL_INST] = 1;
            init_medeleg_mask[BREAK] = 1;
            init_medeleg_mask[LOAD_ADDR_MISSALIGNED] = 1;
            init_medeleg_mask[LOAD_FAULT] = 1;
            init_medeleg_mask[STORE_AMO_ADDR_MISSALIGNED] = 1;
            init_medeleg_mask[STORE_AMO_FAULT] = 1;
            init_medeleg_mask[ECALL_U] = 1;
            init_medeleg_mask[INST_PAGE_FAULT] = 1;
            init_medeleg_mask[LOAD_PAGE_FAULT] = 1;
            init_medeleg_mask[STORE_OR_AMO_PAGE_FAULT] = 1;
        end
    endfunction

    function logic [31:0] init_mideleg_mask();
       init_mideleg_mask = 0;
        if (CONFIG.INCLUDE_S_MODE) begin
            init_mideleg_mask[S_SOFTWARE_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
            init_mideleg_mask[S_TIMER_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
            init_mideleg_mask[S_EXTERNAL_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
        end
    endfunction

    function logic [2**ECODE_W-1:0] init_exception_masking_rom();
        init_exception_masking_rom = '{default: 0};
        init_exception_masking_rom[INST_ADDR_MISSALIGNED] = 1;
        init_exception_masking_rom[INST_ACCESS_FAULT] = CONFIG.INCLUDE_S_MODE;
        init_exception_masking_rom[ILLEGAL_INST] = 1;
        init_exception_masking_rom[BREAK] = 1;
        init_exception_masking_rom[LOAD_ADDR_MISSALIGNED] = 1;
        init_exception_masking_rom[LOAD_FAULT] = CONFIG.INCLUDE_S_MODE;
        init_exception_masking_rom[STORE_AMO_ADDR_MISSALIGNED] = 1;
        init_exception_masking_rom[STORE_AMO_FAULT] = CONFIG.INCLUDE_S_MODE;
        init_exception_masking_rom[ECALL_U] = CONFIG.INCLUDE_S_MODE;
        init_exception_masking_rom[ECALL_S] = CONFIG.INCLUDE_S_MODE;
        init_exception_masking_rom[ECALL_M] = 1;
        init_exception_masking_rom[INST_PAGE_FAULT] = CONFIG.INCLUDE_S_MODE;
        init_exception_masking_rom[LOAD_PAGE_FAULT] = CONFIG.INCLUDE_S_MODE;
        init_exception_masking_rom[STORE_OR_AMO_PAGE_FAULT] = CONFIG.INCLUDE_S_MODE;
    endfunction

    function logic [2**ECODE_W-1:0] init_interrupt_masking_rom();
        init_interrupt_masking_rom = '{default: 0};
        init_interrupt_masking_rom[S_SOFTWARE_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
        init_interrupt_masking_rom[M_SOFTWARE_INTERRUPT] = 1;
        init_interrupt_masking_rom[S_TIMER_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
        init_interrupt_masking_rom[M_TIMER_INTERRUPT] = 1;
        init_interrupt_masking_rom[S_EXTERNAL_INTERRUPT] = CONFIG.INCLUDE_S_MODE;
        init_interrupt_masking_rom[M_EXTERNAL_INTERRUPT] = 1;
    endfunction

    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Decode
    assign unit_needed = decode_stage.instruction inside {CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI};
    always_comb begin
        uses_rs = '0;
        uses_rs[RS1] = decode_stage.instruction inside {CSRRW, CSRRS, CSRRC};
        uses_rd = unit_needed;
    end
    ////////////////////////////////////////////////////
    //Issue
    assign csr_inputs = '{
        addr : issue_stage.instruction[31:20],
        op : issue_stage.fn3[1:0],
        data : issue_stage.fn3[2] ? {27'b0, issue_rs_addr[RS1]} : rf[RS1],
        reads : ~((issue_stage.fn3[1:0] == CSR_RW) && (issue_stage.rd_addr == 0)),
        writes : ~((issue_stage.fn3[1:0] == CSR_RC) && (issue_rs_addr[RS1] == 0))
    };

    assign processing_csr = busy | issue.new_request;
    
    assign issue.ready = ~busy;

    always_ff @(posedge clk) begin
        if (rst)
            busy <= 0;
        else
            busy <= (busy & ~wb.ack) | issue.new_request;
    end

    always_ff @(posedge clk) begin
        if (issue.new_request)
            csr_inputs_r <= csr_inputs;
    end

    always_ff @(posedge clk) begin
        if (rst)
            commit_in_progress <= 0;
        else
            commit_in_progress <= (commit_in_progress & ~issue.new_request) | commit;
    end

    //Waits until CSR instruction is the oldest issued instruction
    assign commit = (retire_ids[0] == wb.id) & busy & (~commit_in_progress);

    ////////////////////////////////////////////////////
    //Output

    always_ff @(posedge clk) begin
        if (rst)
            wb.done <= 0;
        else
            wb.done <= (wb.done & ~wb.ack) | commit;
    end

    always_ff @(posedge clk) begin
        if (issue.new_request)
            wb.id <= issue.id;
    end

    assign wb.rd = selected_csr_r;

    ////////////////////////////////////////////////////
    //Shared logic 
    always_ff @(posedge clk) begin
        sub_write_en <= (1 << csr_inputs_r.addr.sub_addr);
        mwrite <= CONFIG.INCLUDE_M_MODE && commit && (csr_inputs_r.addr.rw_bits != CSR_READ_ONLY && csr_inputs_r.addr.privilege == MACHINE_PRIVILEGE);
        swrite <= CONFIG.INCLUDE_S_MODE && commit && (csr_inputs_r.addr.rw_bits != CSR_READ_ONLY && csr_inputs_r.addr.privilege == SUPERVISOR_PRIVILEGE);
    end

    always_ff @(posedge clk) begin
        if (commit) begin
            case (csr_inputs_r.op)
                CSR_RW : updated_csr = csr_inputs_r.data;
                CSR_RS : updated_csr = selected_csr | csr_inputs_r.data;
                CSR_RC : updated_csr = selected_csr & ~csr_inputs_r.data;
                default : updated_csr = csr_inputs_r.data;
            endcase
        end
    end

    ////////////////////////////////////////////////////
    //Machine Mode Registers
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Constant Registers

    ////////////////////////////////////////////////////
    //Machine ISA register
    localparam misa_t misa = '{
        default:0,
        mxlen:1,
        A:(CONFIG.INCLUDE_AMO),
        I:1,
        M:(CONFIG.INCLUDE_UNIT.MUL && CONFIG.INCLUDE_UNIT.DIV),
        S:(CONFIG.INCLUDE_S_MODE),
        U:(CONFIG.INCLUDE_U_MODE)
    };

    ////////////////////////////////////////////////////
    //Machine Version Registers
    localparam logic [31:0] mvendorid = 0;
    localparam logic [31:0] marchid = 0;
    localparam logic [31:0] mimpid = CONFIG.CSRS.MACHINE_IMPLEMENTATION_ID;
    localparam logic [31:0] mhartid = CONFIG.CSRS.CPU_ID;

    ////////////////////////////////////////////////////
    //MSTATUS
    localparam logic [31:0] mstatush = 0; //Always little endian

    ////////////////////////////////////////////////////
    //Non-Constant Registers
    mstatus_t mstatus;
    logic[31:0] mtvec;
    logic[31:0] medeleg;
    logic[31:0] mideleg;
    logic[31:0] mepc;
    mip_t mip, mip_new;
    mie_t mie;
    mcause_t mcause;
    logic[31:0] mtval;
    logic[31:0] mscratch;

    //Virtualization support: TSR, TW, TVM unused
    //Extension context status: SD, FS, XS unused
    localparam mstatus_t mstatus_mask = '{
        default:0,
        mprv:(CONFIG.INCLUDE_U_MODE | CONFIG.INCLUDE_S_MODE),
        mxr:(CONFIG.INCLUDE_S_MODE),
        sum:(CONFIG.INCLUDE_U_MODE & CONFIG.INCLUDE_S_MODE),
        mpp:'1,
        spp:(CONFIG.INCLUDE_S_MODE),
        mpie:1,
        spie:(CONFIG.INCLUDE_S_MODE),
        mie:1,
        sie:(CONFIG.INCLUDE_S_MODE)
    };

    localparam mstatus_t sstatus_mask = '{default:0, mxr:1, sum:1, spp:1, spie:1, sie:1};

    localparam mip_t sip_mask = '{default:0, seip:CONFIG.INCLUDE_S_MODE, stip:CONFIG.INCLUDE_S_MODE, ssip:CONFIG.INCLUDE_S_MODE};
    localparam mie_t sie_mask = '{default:0, seie:CONFIG.INCLUDE_S_MODE, stie:CONFIG.INCLUDE_S_MODE, ssie:CONFIG.INCLUDE_S_MODE};


generate if (CONFIG.INCLUDE_M_MODE) begin : gen_csr_m_mode
    mstatus_t mstatus_new;
    mstatus_t mstatus_write_mask;
    logic [ECODE_W-1:0] interrupt_cause_r;

    //Interrupt and Exception Delegation
    //Can delegate to supervisor if currently in supervisor or user modes
    logic can_delegate;
    logic exception_delegated;
    logic interrupt_delegated;

    assign can_delegate = CONFIG.INCLUDE_S_MODE & privilege_level inside {SUPERVISOR_PRIVILEGE, USER_PRIVILEGE};
    assign exception_delegated = can_delegate & exception.valid & medeleg[exception.code];
    assign interrupt_delegated = can_delegate & interrupt_taken & mideleg[interrupt_cause_r];

    one_hot_to_integer #(6)
    mstatus_case_one_hot (
        .one_hot ({sret, mret, exception.valid, interrupt_taken, (mwrite_en(MSTATUS) | swrite_en(SSTATUS)), 1'b0}), 
        .int_out (mstatus_case)
    );

    always_comb begin
        case (mstatus_case) inside
            MSTATUS_MRET : next_privilege_level = privilege_t'(mstatus.mpp);
            MSTATUS_SRET : next_privilege_level = privilege_t'({1'b0,mstatus.spp});
            MSTATUS_INTERRUPT : next_privilege_level = interrupt_delegated ? SUPERVISOR_PRIVILEGE : MACHINE_PRIVILEGE;
            MSTATUS_EXCEPTION : next_privilege_level = exception_delegated ? SUPERVISOR_PRIVILEGE : MACHINE_PRIVILEGE;
            default : next_privilege_level = privilege_level;
        endcase
    end

    //Current privilege level
    always_ff @(posedge clk) begin
        if (rst)
            privilege_level <= MACHINE_PRIVILEGE;
        else
            privilege_level <= next_privilege_level;
    end
    assign current_privilege = privilege_level;

    assign mstatus_write_mask = swrite ? sstatus_mask : mstatus_mask;

    always_comb begin
        mstatus_new = mstatus;
        case (mstatus_case) inside
            MSTATUS_WRITE : mstatus_new = (mstatus & ~mstatus_write_mask) | (updated_csr & mstatus_write_mask);
            MSTATUS_MRET : begin
                mstatus_new.mie = mstatus.mpie;
                mstatus_new.mpie = 1;
                mstatus_new.mpp = CONFIG.INCLUDE_U_MODE ? USER_PRIVILEGE : MACHINE_PRIVILEGE;
                if (mstatus.mpp != MACHINE_PRIVILEGE)
                    mstatus_new.mprv = 0;
            end
            MSTATUS_SRET : begin
                mstatus_new.sie = mstatus.spie;
                mstatus_new.spie = 1;
                mstatus_new.spp = USER_PRIVILEGE[0];
                mstatus_new.mprv = 0;
            end
            MSTATUS_INTERRUPT, MSTATUS_EXCEPTION : begin
                if (next_privilege_level == SUPERVISOR_PRIVILEGE) begin
                    mstatus_new.spie = (privilege_level == SUPERVISOR_PRIVILEGE) ? mstatus.sie : 0;
                    mstatus_new.sie = 0;
                    mstatus_new.spp = privilege_level[0]; //one if from supervisor-mode, zero if from user-mode
                end
                else begin
                    mstatus_new.mpie = (privilege_level == MACHINE_PRIVILEGE) ? mstatus.mie : ((privilege_level == SUPERVISOR_PRIVILEGE) ? mstatus.sie : 0);
                    mstatus_new.mie = 0;
                    mstatus_new.mpp = privilege_level; //machine,supervisor or user
                end
            end
            default : mstatus_new = mstatus;
        endcase
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
    initial mtvec[31:2] = CONFIG.CSRS.RESET_MTVEC[31:2];
    always_ff @(posedge clk) begin
        mtvec[1:0] <= '0;
        if (CONFIG.CSRS.NON_STANDARD_OPTIONS.MTVEC_WRITEABLE & mwrite_en(MTVEC))
            mtvec[31:2] <= updated_csr[31:2];
    end
    assign exception_target_pc = mtvec;

    ////////////////////////////////////////////////////
    //MEDELEG
    localparam logic [31:0] medeleg_mask = init_medeleg_mask();
    always_ff @(posedge clk) begin
        if (rst)
            medeleg <= '0;
        else if (mwrite_en(MEDELEG) & CONFIG.INCLUDE_S_MODE)
            medeleg <= (updated_csr & medeleg_mask);
    end

    ////////////////////////////////////////////////////
    //MIDELEG
    localparam logic [31:0] mideleg_mask = init_mideleg_mask();
    always_ff @(posedge clk) begin
        if (rst)
            mideleg <= '0;
        else if (mwrite_en(MIDELEG) & CONFIG.INCLUDE_S_MODE)
            mideleg <= (updated_csr & mideleg_mask);
    end

    ////////////////////////////////////////////////////
    //MIP
    localparam mip_t mip_mask = '{default:0, meip:1, seip:CONFIG.INCLUDE_S_MODE, mtip:1, stip:CONFIG.INCLUDE_S_MODE, msip:1, ssip:CONFIG.INCLUDE_S_MODE};
    localparam mip_t mip_w_mask = '{default:0, seip:CONFIG.INCLUDE_S_MODE, stip:CONFIG.INCLUDE_S_MODE, ssip:CONFIG.INCLUDE_S_MODE};

    always_comb begin
        mip_new = '0;
        mip_new.ssip = s_interrupt.software;
        mip_new.stip = s_interrupt.timer;
        mip_new.seip = s_interrupt.external;

        mip_new.msip = m_interrupt.software;
        mip_new.mtip = m_interrupt.timer;
        mip_new.meip = m_interrupt.external;

        mip_new &= mip_mask;
    end
    
    always_ff @(posedge clk) begin
        if (rst)
            mip <= 0;
        else if (mwrite_en(MIP) | (|mip_new))
            mip <= (updated_csr & mip_w_mask) | mip_new;
    end
    assign interrupt_pending = |(mip & mie) & mstatus.mie;

    ////////////////////////////////////////////////////
    //MIE
    localparam mie_t mie_mask = '{default:0, meie:1, seie:CONFIG.INCLUDE_S_MODE, mtie:1, stie:CONFIG.INCLUDE_S_MODE, msie:1, ssie:CONFIG.INCLUDE_S_MODE};
    always_ff @(posedge clk) begin
        if (rst)
            mie <= '0;
        else if (mwrite_en(MIE) | swrite_en(SIE))
            mie <= updated_csr & (swrite ? sie_mask : mie_mask);
    end

    ////////////////////////////////////////////////////
    //MEPC
    //Can be software written, written on exception with
    //exception causing PC.  Lower two bits tied to zero.
    always_ff @(posedge clk) begin
        mepc[1:0] <= '0;
        if (mwrite_en(MEPC) | exception.valid | interrupt_taken)
            mepc[31:2] <= (exception.valid | interrupt_taken) ? exception.pc[31:2] : updated_csr[31:2];
    end
    assign epc = mepc;


    ////////////////////////////////////////////////////
    //MCAUSE
    //As the exception and interrupts codes are sparsely populated,
    //to ensure that only legal values are written, a ROM lookup
    //is used to validate the CSR write operation
    localparam logic [2**ECODE_W-1:0] M_EXCEPTION_MASKING_ROM = init_exception_masking_rom();
    localparam logic [2**ECODE_W-1:0] M_INTERRUPT_MASKING_ROM  = init_interrupt_masking_rom();

    logic mcause_write_valid;
    always_comb begin
        if (updated_csr[31]) //interrupt
            mcause_write_valid = M_INTERRUPT_MASKING_ROM[updated_csr[ECODE_W-1:0]];
        else
            mcause_write_valid = M_EXCEPTION_MASKING_ROM[updated_csr[ECODE_W-1:0]];
    end

    mip_t mip_cause;
    logic [5:0] mip_priority_vector;
    logic [2:0] mip_cause_sel;

    localparam logic [ECODE_W-1:0] interruput_code_table [7:0] = '{ 0, 0, 
        M_EXTERNAL_INTERRUPT, M_TIMER_INTERRUPT, M_SOFTWARE_INTERRUPT,
        S_EXTERNAL_INTERRUPT, S_TIMER_INTERRUPT, S_SOFTWARE_INTERRUPT
    };
    assign mip_cause = (mip & mie);
    assign mip_priority_vector = '{mip_cause.meip, mip_cause.mtip, mip_cause.msip, mip_cause.seip, mip_cause.stip, mip_cause.ssip};

    priority_encoder #(.WIDTH(6))
    interrupt_cause_encoder (
        .priority_vector (mip_priority_vector),
        .encoded_result (mip_cause_sel)
    );

    always_ff @(posedge clk) begin
        if (interrupt_pending)
            interrupt_cause_r <= interruput_code_table[mip_cause_sel];
    end

    always_ff @(posedge clk) begin
        mcause.zeroes <= '0;
        if (rst) begin
            mcause.is_interrupt <= 0;
            mcause.code <= 0;
        end
        else if (CONFIG.CSRS.NON_STANDARD_OPTIONS.INCLUDE_MCAUSE & ((mcause_write_valid & mwrite_en(MCAUSE)) | exception.valid | interrupt_taken)) begin
            mcause.is_interrupt <= interrupt_taken | (mwrite_en(MCAUSE) & updated_csr[31]);
            mcause.code <= interrupt_taken ? interrupt_cause_r : exception.valid ? exception.code : updated_csr[ECODE_W-1:0];
        end
    end

    ////////////////////////////////////////////////////
    //MTVAL
    always_ff @(posedge clk) begin
        if (CONFIG.CSRS.NON_STANDARD_OPTIONS.INCLUDE_MTVAL & (mwrite_en(MTVAL) | exception.valid))
            mtval <=  exception.valid ? exception.tval : updated_csr;
    end

    ////////////////////////////////////////////////////
    //MSCRATCH
    always_ff @(posedge clk) begin
        if (CONFIG.CSRS.NON_STANDARD_OPTIONS.INCLUDE_MSCRATCH & mwrite_en(MSCRATCH))
            mscratch <= updated_csr;
    end

end
endgenerate

    ////////////////////////////////////////////////////
    //END OF MACHINE REGS
    ////////////////////////////////////////////////////












    ////////////////////////////////////////////////////
    //BEGIN OF SUPERVISOR REGS
    ////////////////////////////////////////////////////
    logic[31:0] sepc;

    logic[31:0] stime;
    logic[31:0] stimecmp;

    logic[31:0] scause;
    logic[31:0] stval;

    logic[31:0] sstatus;
    logic[31:0] stvec;

    satp_t satp;

    logic[31:0] sscratch;

    //TLB status --- used to mux physical/virtual address
    assign tlb_on = CONFIG.INCLUDE_S_MODE & satp.mode;
    assign asid = satp.asid;
    //******************

generate if (CONFIG.INCLUDE_S_MODE) begin : gen_csr_s_mode
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

    ////////////////////////////////////////////////////
    //STVEC
    logic [31:0] stvec_mask = '1;
    always_ff @(posedge clk) begin
        if (rst)
            stvec <= {CONFIG.CSRS.RESET_VEC[31:2], 2'b00};
        else if (swrite_en(STVEC))
            stvec <= (updated_csr & stvec_mask);
    end

    ////////////////////////////////////////////////////
    //SATP
    logic[31:0] satp_mask;
    assign satp_mask = '1;
    always_ff @(posedge clk) begin
        if (rst)
            satp <= 0;
        else if (swrite_en(SATP))
            satp <= (updated_csr & satp_mask);
    end

    ////////////////////////////////////////////////////
    //SSCRATCH
    always_ff @(posedge clk) begin
        if (swrite_en(SSCRATCH))
            sscratch <= updated_csr;
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
    localparam COUNTER_W = CONFIG.CSRS.NON_STANDARD_OPTIONS.COUNTER_W;
    localparam MCYCLE_WRITEABLE = CONFIG.CSRS.NON_STANDARD_OPTIONS.MCYCLE_WRITEABLE;
    localparam MINSTR_WRITEABLE = CONFIG.CSRS.NON_STANDARD_OPTIONS.MINSTR_WRITEABLE;

    logic[COUNTER_W-1:0] mcycle;
    logic[COUNTER_W-1:0] mtime;
    logic[COUNTER_W-1:0] minst_ret;

    logic[COUNTER_W-1:0] mcycle_input_next;
    logic[COUNTER_W-1:0] minst_ret_input_next;
    logic[LOG2_RETIRE_PORTS:0] minst_ret_inc;
    logic mcycle_inc;

    assign mcycle_input_next[31:0] = (MCYCLE_WRITEABLE & mwrite_en(MCYCLE)) ? updated_csr : mcycle[31:0];
    assign mcycle_input_next[COUNTER_W-1:32] = (MCYCLE_WRITEABLE & mwrite_en(MCYCLE)) ? updated_csr[COUNTER_W-33:0] : mcycle[COUNTER_W-1:32];
    assign mcycle_inc = ~(MCYCLE_WRITEABLE & (mwrite_en(MCYCLE) | mwrite_en(MCYCLEH)));

    always_ff @(posedge clk) begin
        if (rst) 
            mcycle <= 0;
        else
            mcycle <= mcycle_input_next + COUNTER_W'(mcycle_inc);
    end

    assign minst_ret_input_next[31:0] = (MINSTR_WRITEABLE & mwrite_en(MINSTRET)) ? updated_csr : minst_ret[31:0];
    assign minst_ret_input_next[COUNTER_W-1:32] = (MINSTR_WRITEABLE & mwrite_en(MINSTRET)) ? updated_csr[COUNTER_W-33:0] : minst_ret[COUNTER_W-1:32];
    assign minst_ret_inc = (MINSTR_WRITEABLE & (mwrite_en(MINSTRET) | mwrite_en(MINSTRETH))) ? '0 : retire_count;
    
    always_ff @(posedge clk) begin
        if (rst)
            minst_ret <= 0;
        else
            minst_ret <= minst_ret_input_next + COUNTER_W'(minst_ret_inc);
    end


    ////////////////////////////////////////////////////
    //CSR mux
    logic [31:0] read_mask;
    always_comb begin
        case (csr_inputs_r.addr) inside
            SSTATUS : read_mask = CONFIG.INCLUDE_S_MODE ? sstatus_mask : '1;
            SIE : read_mask = CONFIG.INCLUDE_S_MODE ? sie_mask : '1;
            SIP : read_mask = CONFIG.INCLUDE_S_MODE ? sip_mask : '1;
            default : read_mask = '1;
        endcase
    end
    always_comb begin
        case (csr_inputs_r.addr) inside
            //Machine info
            MISA :  selected_csr = CONFIG.INCLUDE_M_MODE ? misa : '0;
            MVENDORID : selected_csr = CONFIG.INCLUDE_M_MODE ? mvendorid : '0;
            MARCHID : selected_csr = CONFIG.INCLUDE_M_MODE ? marchid : '0;
            MIMPID : selected_csr = CONFIG.INCLUDE_M_MODE ? mimpid : '0;
            MHARTID : selected_csr = CONFIG.INCLUDE_M_MODE ? mhartid : '0;
            //Machine trap setup
            MSTATUS : selected_csr = CONFIG.INCLUDE_M_MODE ? mstatus : '0;
            MEDELEG : selected_csr = CONFIG.INCLUDE_M_MODE ? medeleg : '0;
            MIDELEG : selected_csr = CONFIG.INCLUDE_M_MODE ? mideleg : '0;
            MIE : selected_csr = CONFIG.INCLUDE_M_MODE ? mie : '0;
            MTVEC : selected_csr = CONFIG.INCLUDE_M_MODE ? mtvec : '0;
            MCOUNTEREN : selected_csr = '0;
            //Machine trap handling
            MSCRATCH : selected_csr = CONFIG.INCLUDE_M_MODE ? mscratch : '0;
            MEPC : selected_csr = CONFIG.INCLUDE_M_MODE ? mepc : '0;
            MCAUSE : selected_csr = CONFIG.INCLUDE_M_MODE ? mcause : '0;
            MTVAL : selected_csr = CONFIG.INCLUDE_M_MODE ? mtval : '0;
            MIP : selected_csr = CONFIG.INCLUDE_M_MODE ? mip : '0;
            //Machine Memory Protection
            [12'h3EF : 12'h3A0] : selected_csr = '0;
            //Machine Timers and Counters
            MCYCLE : selected_csr = CONFIG.INCLUDE_M_MODE ? mcycle[31:0] : '0;
            MINSTRET : selected_csr = CONFIG.INCLUDE_M_MODE ? minst_ret[31:0] : '0;
            [12'hB03 : 12'hB1F] : selected_csr = '0;
            MCYCLEH : selected_csr = CONFIG.INCLUDE_M_MODE ? 32'(mcycle[COUNTER_W-1:32]) : '0;
            MINSTRETH : selected_csr = CONFIG.INCLUDE_M_MODE ? 32'(minst_ret[COUNTER_W-1:32]) : '0;
            [12'hB83 : 12'hB9F] : selected_csr = '0;
            //Machine Counter Setup
            [12'h320 : 12'h33F] : selected_csr = '0;

            //Supervisor Trap Setup
            SSTATUS : selected_csr = CONFIG.INCLUDE_S_MODE ? mstatus : '0;
            SEDELEG : selected_csr = '0; //No user-level interrupts/exception handling
            SIDELEG : selected_csr = '0;
            SIE : selected_csr = CONFIG.INCLUDE_S_MODE ? mie : '0;
            STVEC : selected_csr = CONFIG.INCLUDE_S_MODE ? stvec : '0;
            SCOUNTEREN : selected_csr = '0;
            //Supervisor trap handling
            SSCRATCH : selected_csr = CONFIG.INCLUDE_S_MODE ? sscratch : '0;
            SEPC : selected_csr = CONFIG.INCLUDE_S_MODE ? sscratch : '0;
            SCAUSE : selected_csr = CONFIG.INCLUDE_S_MODE ? sscratch : '0;
            STVAL : selected_csr = CONFIG.INCLUDE_S_MODE ? sscratch : '0;
            SIP : selected_csr = CONFIG.INCLUDE_S_MODE ? mip : '0;
            //Supervisor Protection and Translation
            SATP : selected_csr = CONFIG.INCLUDE_S_MODE ? satp : '0;

            //User status
            //Floating point
            FFLAGS : selected_csr = '0;
            FRM : selected_csr = '0;
            FCSR : selected_csr = '0;
            //User Counter Timers
            CYCLE : selected_csr = mcycle[31:0];
            TIME : selected_csr = mcycle[31:0];
            INSTRET : selected_csr = minst_ret[31:0];
            [12'hC03 : 12'hC1F] : selected_csr = '0;
            CYCLEH : selected_csr = 32'(mcycle[COUNTER_W-1:32]);
            TIMEH : selected_csr = 32'(mcycle[COUNTER_W-1:32]);
            INSTRETH : selected_csr = 32'(minst_ret[COUNTER_W-1:32]);
            [12'hC83 : 12'hC9F] : selected_csr = '0;

            default : selected_csr = '0;
        endcase
    end
    always_ff @(posedge clk) begin
        if (commit)
            selected_csr_r <= selected_csr & read_mask;
    end

    ////////////////////////////////////////////////////
    //Assertions
    mstatus_update_assertion:
        assert property (@(posedge clk) disable iff (rst) $onehot0({mret,sret,interrupt_taken, exception.valid,(mwrite_en(MSTATUS) | swrite_en(SSTATUS))})) else $error("multiple write to mstatus");

endmodule
