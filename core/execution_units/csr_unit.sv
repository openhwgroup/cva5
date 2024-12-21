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
        input logic instruction_issued,
        input logic fp_instruction_issued_with_rd,

        //Unit Interfaces
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb,

        //Privilege
        output logic [1:0] current_privilege,
        output envcfg_t menvcfg,
        output envcfg_t senvcfg,
        
        //FP
        input logic [4:0] fflag_wmask, //Always valid
        output logic [2:0] dyn_rm,

        //GC
        input logic interrupt_taken,
        output logic interrupt_pending,
        output logic csr_frontend_flush,

        //TLB and MMU
        output logic instruction_translation_on,
        output logic data_translation_on,
        output logic [ASIDLEN-1:0] asid,

        //MMUs
        mmu_interface.csr immu,
        mmu_interface.csr dmmu,

        //CSR exception interface
        input exception_packet_t exception_pkt,
        output logic [31:0] exception_target_pc,

        //exception return
        input logic mret,
        input logic sret,
        output logic [31:0] mepc,
        output logic [31:0] sepc,
        
        //Exception generation
        exception_interface.unit exception,

        //Retire
        input id_t retire_ids [RETIRE_PORTS],

        //External
        input logic [63:0] mtime,
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
    logic illegal_instruction;

    logic [31:0] selected_csr;
    logic [31:0] selected_csr_r;

    logic [31:0] updated_csr;
    logic [31:0] next_csr;

    logic exception_delegated;
    logic interrupt_delegated;
    logic [ECODE_W-1:0] interrupt_cause_r;

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
        if (CONFIG.MODES == MSU) begin
            init_medeleg_mask[INST_ADDR_MISSALIGNED] = 1;
            init_medeleg_mask[INST_ACCESS_FAULT] = 1;
            init_medeleg_mask[ILLEGAL_INST] = 1;
            init_medeleg_mask[BREAK] = 1;
            init_medeleg_mask[LOAD_ADDR_MISSALIGNED] = 1;
            init_medeleg_mask[LOAD_FAULT] = 1;
            init_medeleg_mask[STORE_AMO_ADDR_MISSALIGNED] = 1;
            init_medeleg_mask[STORE_AMO_FAULT] = 1;
            init_medeleg_mask[ECALL_U] = 1;
            init_medeleg_mask[ECALL_S] = 1;
            init_medeleg_mask[INST_PAGE_FAULT] = 1;
            init_medeleg_mask[LOAD_PAGE_FAULT] = 1;
            init_medeleg_mask[STORE_OR_AMO_PAGE_FAULT] = 1;
        end
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
        reads : ~((issue_stage.fn3[1:0] == CSR_RW) & (issue_stage.rd_addr == 0)),
        writes : ~((issue_stage.fn3[1:0] != CSR_RW) & (issue_rs_addr[RS1] == 0))
    };
    
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
        mwrite <= CONFIG.MODES != BARE & commit & (csr_inputs_r.addr.rw_bits != CSR_READ_ONLY & csr_inputs_r.addr.privilege == MACHINE_PRIVILEGE) & ~illegal_instruction;
        swrite <= CONFIG.MODES == MSU & commit & (csr_inputs_r.addr.rw_bits != CSR_READ_ONLY & csr_inputs_r.addr.privilege == SUPERVISOR_PRIVILEGE) & ~illegal_instruction;
    end

    always_comb begin
        case (csr_inputs_r.op)
            CSR_RW : next_csr = csr_inputs_r.data;
            CSR_RS : next_csr = selected_csr | csr_inputs_r.data;
            CSR_RC : next_csr = selected_csr & ~csr_inputs_r.data;
            default : next_csr = csr_inputs_r.data;
        endcase
    end

    always_ff @(posedge clk) begin
        if (commit)
            updated_csr <= next_csr;
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
        M:(CONFIG.INCLUDE_UNIT.MUL & CONFIG.INCLUDE_UNIT.DIV),
        S:(CONFIG.MODES == MSU),
        U:(CONFIG.MODES inside {MU, MSU}),
        F:(CONFIG.INCLUDE_UNIT.FPU),
        D:(CONFIG.INCLUDE_UNIT.FPU)
    };

    ////////////////////////////////////////////////////
    //Machine Version Registers
    localparam logic [31:0] mvendorid = 0;
    localparam logic [31:0] marchid = 0; //TODO: register an ID with RISC-V
    localparam logic [31:0] mimpid = CONFIG.CSRS.MACHINE_IMPLEMENTATION_ID;
    localparam logic [31:0] mhartid = CONFIG.CSRS.CPU_ID;
    localparam logic [31:0] mconfigptr = CONFIG.CSRS.MCONFIGPTR;

    ////////////////////////////////////////////////////
    //Constants
    localparam logic [31:0] mstatush = 0; //Always little endian
    localparam logic [31:0] medelegh = 0; //Not used
    localparam logic [31:0] mstateen0 = 0; //Behaviour defined but not relevant
    localparam logic [31:0] mstateen1 = 0; //Behaviour not yet defined
    localparam logic [31:0] mstateen2 = 0; //Behaviour not yet defined
    localparam logic [31:0] mstateen3 = 0; //Behaviour not yet defined
    localparam logic [31:0] mstateen1h = 0; //Behaviour not yet defined
    localparam logic [31:0] mstateen2h = 0; //Behaviour not yet defined
    localparam logic [31:0] mstateen3h = 0; //Behaviour not yet defined

    ////////////////////////////////////////////////////
    //Non-Constant Registers
    mstatus_t mstatus;
    logic[31:0] mtvec;
    logic[31:0] medeleg;
    mideleg_t mideleg;
    mip_t mip;
    mie_t mie;
    cause_t mcause;
    logic[31:0] mtval;
    logic[31:0] mscratch;
    mcounter_t mcounteren;
    mcounter_t mcountinhibit;
    envcfgh_t menvcfgh;
    mstateen0h_t mstateen0h;

    //Virtualization support: TSR, TW, TVM unused
    //Extension context status: XS unused
    localparam mstatus_t mstatus_mask = '{
        default:0,
        mprv:(CONFIG.MODES inside {MU, MSU}),
        mxr:(CONFIG.MODES == MSU),
        sum:(CONFIG.MODES == MSU),
        mpp:'1,
        spp:(CONFIG.MODES == MSU),
        mpie:1,
        spie:(CONFIG.MODES == MSU),
        mie:1,
        sie:(CONFIG.MODES == MSU),
        sd:(CONFIG.INCLUDE_UNIT.FPU),
        fs:{2{CONFIG.INCLUDE_UNIT.FPU}}
    };

    localparam mstatus_t sstatus_mask = '{default:0, mxr:1, sum:1, spp:1, spie:1, sie:1, sd:(CONFIG.INCLUDE_UNIT.FPU), fs:{2{CONFIG.INCLUDE_UNIT.FPU}}};
    logic stip_stimecmp;

    logic[31:0] sie;
    mip_t sip;
    mie_t sie_deleg_mask;
    localparam mie_t sie_mask = '{default:0, seie:CONFIG.MODES == MSU, stie:CONFIG.MODES == MSU, ssie:CONFIG.MODES == MSU};
    localparam mip_t sip_mask = '{default:0, seip:CONFIG.MODES == MSU, stip:CONFIG.MODES == MSU, ssip:CONFIG.MODES == MSU};


generate if (CONFIG.MODES != BARE) begin : gen_csr_m_mode
    mstatus_t mstatus_new;
    mstatus_t mstatus_write_mask;
    logic[4:0] fflag_wmask_r; //Used for updating mstatus, registered for frequency reasons

    always_ff @(posedge clk) begin
        if (rst)
            fflag_wmask_r <= '0;
        else if (CONFIG.INCLUDE_UNIT.FPU)
            fflag_wmask_r <= fflag_wmask;
    end

    //Interrupt and Exception Delegation
    //Can delegate to supervisor if currently in supervisor or user modes
    logic can_delegate;

    assign can_delegate = CONFIG.MODES == MSU & privilege_level inside {SUPERVISOR_PRIVILEGE, USER_PRIVILEGE};
    assign exception_delegated = can_delegate & exception_pkt.valid & medeleg[exception_pkt.code];
    assign interrupt_delegated = can_delegate & interrupt_taken & mideleg[interrupt_cause_r];

    one_hot_to_integer #(6)
    mstatus_case_one_hot (
        .one_hot ({sret, mret, exception_pkt.valid, interrupt_taken, (mwrite_en(MSTATUS) | swrite_en(SSTATUS)), 1'b0}), 
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
            MSTATUS_WRITE : begin 
                mstatus_new = (mstatus & ~mstatus_write_mask) | (updated_csr & mstatus_write_mask);
                //Cannot write invalid privilege
                if (CONFIG.MODES == M)
                    mstatus_new.mpp = MACHINE_PRIVILEGE;
                else if (CONFIG.MODES == MU & ^mstatus_new.mpp)
                    mstatus_new.mpp = MACHINE_PRIVILEGE;
                else if (CONFIG.MODES == MSU & mstatus_new.mpp == RESERVED_PRIVILEGE)
                    mstatus_new.mpp = MACHINE_PRIVILEGE;
            end
            MSTATUS_MRET : begin
                mstatus_new.mie = mstatus.mpie;
                mstatus_new.mpie = 1;
                mstatus_new.mpp = CONFIG.MODES inside {MU, MSU} ? USER_PRIVILEGE : MACHINE_PRIVILEGE;
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
                    mstatus_new.spie = mstatus.sie;
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

        //Overwrites writes to fs and sd from above
        if (CONFIG.INCLUDE_UNIT.FPU) begin
            if (fp_instruction_issued_with_rd | |fflag_wmask_r | (commit & csr_inputs_r.addr inside {FFLAGS, FRM, FCSR})) begin
                mstatus_new.fs = 2'b11;
                mstatus_new.sd = 1'b1;
            end
            else if (mwrite_en(MSTATUS) | swrite_en(SSTATUS)) begin
                mstatus_new.fs = |updated_csr[14:13] ? updated_csr[14:13] : mstatus.fs; //Cannot disable by writing 00
                mstatus_new.sd = &updated_csr[14:13];
            end
            else begin
                mstatus_new.fs = mstatus.fs;
                mstatus_new.sd = mstatus.sd;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (rst)
            mstatus <= '{default:0, mpp:MACHINE_PRIVILEGE, fs:{1'b0, CONFIG.INCLUDE_UNIT.FPU}};
        else
            mstatus <= mstatus_new;
    end

    ////////////////////////////////////////////////////
    //MTVEC
    //No vectored mode, mode hard-coded to zero
    always_ff @(posedge clk) begin
        mtvec[1:0] <= '0;
        if (rst)
            mtvec[31:2] <= CONFIG.CSRS.RESET_TVEC[31:2];
        else if (mwrite_en(MTVEC))
            mtvec[31:2] <= updated_csr[31:2];
    end

    ////////////////////////////////////////////////////
    //MEDELEG
    localparam logic [31:0] medeleg_mask = init_medeleg_mask();
    always_ff @(posedge clk) begin
        if (rst)
            medeleg <= '0;
        else if (mwrite_en(MEDELEG) & CONFIG.MODES == MSU)
            medeleg <= updated_csr & medeleg_mask;
    end

    ////////////////////////////////////////////////////
    //MIDELEG
    localparam mideleg_t mideleg_mask = '{default:0, ssid:CONFIG.MODES == MSU, stid:CONFIG.MODES == MSU, seid:CONFIG.MODES == MSU};
    always_ff @(posedge clk) begin
        if (rst)
            mideleg <= '0;
        else if (mwrite_en(MIDELEG) & CONFIG.MODES == MSU)
            mideleg <= updated_csr & mideleg_mask;
    end

    ////////////////////////////////////////////////////
    //MIP
    //Bits tracked separately
    logic meip;
    logic mtip;
    logic msip;

    //SIP is part of MIP
    logic seip;
    logic stip;
    logic ssip;

    assign mip = '{
        meip: meip,
        mtip: mtip,
        msip: msip,
        seip: CONFIG.MODES == MSU & seip,
        stip: CONFIG.MODES == MSU & stip,
        ssip: CONFIG.MODES == MSU & ssip,
        default:0
    };

    always_ff @(posedge clk) begin
        meip <= m_interrupt.external;
        mtip <= m_interrupt.timer;
        msip <= m_interrupt.software;
    end

if (CONFIG.MODES == MSU) begin : gen_supervisor_interrupts
    logic seip_r;
    logic seip_external;
    logic seip_next;
    mip_t seip_next_casted;
    
    //SEIP depends on an external and writable signal
    assign seip_next_casted = mip_t'(csr_inputs_r.data);
    assign seip = seip_r | seip_external;

    always_ff @(posedge clk) begin
        seip_external <= s_interrupt.external;
        case (csr_inputs_r.op)
            CSR_RW : seip_next <= seip_next_casted.seip;
            CSR_RS : seip_next <= seip_r | seip_next_casted.seip;
            CSR_RC : seip_next <= seip_r & ~seip_next_casted.seip;
            default : seip_next <= seip_next_casted.seip;
        endcase
    end

    //STIP set locally, SSIP set locally or externally
    mip_t updated_csr_mip_casted;
    assign updated_csr_mip_casted = mip_t'(updated_csr);

    always_ff @(posedge clk) begin
        if (rst) begin
            seip_r <= 0;
            stip <= 0;
            ssip <= 0;
        end
        else begin
            //SEIP
            if (mwrite_en(MIP))
                seip_r <= seip_next;
            
            //STIP
            if (CONFIG.CSRS.INCLUDE_SSTC & menvcfgh.stce)
                stip <= stip_stimecmp;
            else if (mwrite_en(MIP))
                stip <= updated_csr_mip_casted.stip;
            
            //SSIP
            if (s_interrupt.software)
                ssip <= 1;
            else if (mwrite_en(MIP) | (swrite_en(SIP) & mideleg.ssid))
                ssip <= updated_csr_mip_casted.ssip;
        end
    end
end

    ////////////////////////////////////////////////////
    //MIE
    localparam mie_t mie_mask = '{default:0, meie:1, mtie:1, msie:1};
    always_ff @(posedge clk) begin
        if (rst)
            mie <= '0;
        else if (mwrite_en(MIE))
            mie <= updated_csr & (mie_mask | sie_mask);
        else if (swrite_en(SIE))
            mie <= (mie & mie_mask) | (updated_csr & sie_deleg_mask);
    end

    always_comb begin
        interrupt_pending = 0;
        //M interrupts
        if (privilege_level != MACHINE_PRIVILEGE | mstatus.mie)
            interrupt_pending |= |(mip & mie & ~mideleg);
        //S interrupts
        if (CONFIG.MODES == MSU & ((privilege_level == SUPERVISOR_PRIVILEGE & mstatus.sie) | privilege_level == USER_PRIVILEGE))
            interrupt_pending |= |(sip & sie);
    end

    ////////////////////////////////////////////////////
    //MEPC
    //Can be software written, written on exception with
    //exception causing PC.  Lower two bits tied to zero.
    always_ff @(posedge clk) begin
        mepc[1:0] <= '0;
        if (rst)
            mepc[31:2] <= '0;
        else if (mwrite_en(MEPC) | (exception_pkt.valid & ~exception_delegated) | (interrupt_taken & ~interrupt_delegated))
            mepc[31:2] <= (exception_pkt.valid | interrupt_taken) ? exception_pkt.pc[31:2] : updated_csr[31:2];
    end

    ////////////////////////////////////////////////////
    //MCAUSE
    //Can be software written, written on exception or
    //interrupt with specific code
    logic [5:0] mip_priority_vector;
    logic [2:0] mip_cause_sel;

    localparam logic [ECODE_W-1:0] interruput_code_table [7:0] = '{ 0, 0, 
        S_TIMER_INTERRUPT, S_SOFTWARE_INTERRUPT, S_EXTERNAL_INTERRUPT,
        M_TIMER_INTERRUPT, M_SOFTWARE_INTERRUPT, M_EXTERNAL_INTERRUPT
    };

    assign mip_priority_vector[0] = mip.meip & mie.meie;
    assign mip_priority_vector[1] = mip.msip & mie.msie;
    assign mip_priority_vector[2] = mip.mtip & mie.mtie;
    assign mip_priority_vector[3] = mip.seip & mie.seie & ~(privilege_level == MACHINE_PRIVILEGE & mideleg.seid); //Suppressed if delegated
    assign mip_priority_vector[4] = mip.ssip & mie.ssie & ~(privilege_level == MACHINE_PRIVILEGE & mideleg.ssid); //Suppressed if delegated
    assign mip_priority_vector[5] = 1;

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
        mcause.zeros <= '0;
        if (rst) begin
            mcause.is_interrupt <= 0;
            mcause.code <= '0;
        end
        else if ((mwrite_en(MCAUSE) | (exception_pkt.valid & ~exception_delegated) | (interrupt_taken & ~interrupt_delegated))) begin
            mcause.is_interrupt <= interrupt_taken | (mwrite_en(MCAUSE) & updated_csr[31]);
            mcause.code <= interrupt_taken ? interrupt_cause_r : exception_pkt.valid ? exception_pkt.code : updated_csr[ECODE_W-1:0];
        end
    end

    ////////////////////////////////////////////////////
    //MTVAL
    always_ff @(posedge clk) begin
        if (rst)
            mtval <= '0;
        else if (mwrite_en(MTVAL) | (exception_pkt.valid & ~exception_delegated))
            mtval <= exception_pkt.valid ? exception_pkt.tval : updated_csr;
    end

    ////////////////////////////////////////////////////
    //MSCRATCH
    always_ff @(posedge clk) begin
        if (rst)
            mscratch <= '0;
        else if (mwrite_en(MSCRATCH))
            mscratch <= updated_csr;
    end

    ////////////////////////////////////////////////////
    //MCOUNTINHIBIT
    localparam mcounter_t mcountinhibit_mask = '{default:0, cy:1, ir:1};
    always_ff @(posedge clk) begin
        if (rst)
            mcountinhibit <= '0;
        else if (mwrite_en(MCOUNTINHIBIT) & CONFIG.MODES == MSU)
            mcountinhibit <= updated_csr & mcountinhibit_mask;
    end

    ////////////////////////////////////////////////////
    //MCOUNTEREN
    localparam mcounter_t mcounteren_mask = '{default:0, cy:1, tm:1, ir:1};
    always_ff @(posedge clk) begin
        if (rst)
            mcounteren <= '0;
        else if (mwrite_en(MCOUNTEREN) & CONFIG.MODES inside {MU, MSU})
            mcounteren <= updated_csr & mcounteren_mask;
    end

    ////////////////////////////////////////////////////
    //MENVCFG
    localparam envcfg_t menvcfg_mask = '{default:0, fiom: 1, cbie:{2{CONFIG.INCLUDE_CBO}}, cbcfe:CONFIG.INCLUDE_CBO};
    always_ff @(posedge clk) begin
        if (rst)
            menvcfg <= '0;
        else if (mwrite_en(MENVCFG) & CONFIG.MODES inside {MU, MSU})
            menvcfg <= updated_csr & menvcfg_mask;
    end

    ////////////////////////////////////////////////////
    //MENVCFGH
    localparam envcfgh_t menvcfgh_mask = '{default:0, stce:CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SSTC};
    always_ff @(posedge clk) begin
        if (rst)
            menvcfgh <= '0;
        else if (mwrite_en(MENVCFGH) & CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SSTC)
            menvcfgh <= updated_csr & menvcfg_mask;
    end

    ////////////////////////////////////////////////////
    //MSTATEEN0H
    localparam mstateen0h_t mstateen0h_mask = '{default:0, se0:CONFIG.MODES == MSU, envcfg:CONFIG.MODES != M};
    always_ff @(posedge clk) begin
        if (rst)
            mstateen0h <= '0;
        else if (mwrite_en(MSTATEEN0H) & CONFIG.MODES != M)
            mstateen0h <= updated_csr & mstateen0h_mask;
    end

end
endgenerate

    ////////////////////////////////////////////////////
    //END OF MACHINE REGS
    ////////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    //BEGIN OF SUPERVISOR REGS
    ////////////////////////////////////////////////////
    cause_t scause;
    logic[31:0] stval;
    logic[31:0] sstatus;
    logic[31:0] stvec;
    satp_t satp;
    logic[31:0] sscratch;
    logic[31:0] scounteren;
    logic[31:0] stimecmp;
    logic[31:0] stimecmph;
    localparam logic[31:0] sstateen0 = 0; //The defined behaviour is not used
    localparam logic[31:0] sstateen1 = 0;
    localparam logic[31:0] sstateen2 = 0;
    localparam logic[31:0] sstateen3 = 0;

    //TLB status --- used to mux physical/virtual address
    assign instruction_translation_on = CONFIG.MODES == MSU & satp.mode & privilege_level != MACHINE_PRIVILEGE;
    assign data_translation_on = CONFIG.MODES == MSU & satp.mode & (privilege_level != MACHINE_PRIVILEGE | (mstatus.mprv & mstatus.mpp != MACHINE_PRIVILEGE));
    assign asid = satp.asid;
    //******************

generate if (CONFIG.MODES == MSU) begin : gen_csr_s_mode
    ////////////////////////////////////////////////////
    //MMU interface
    assign immu.mxr = mstatus.mxr;
    assign dmmu.mxr = mstatus.mxr;
    assign immu.sum = mstatus.sum;
    assign dmmu.sum = mstatus.sum;
    assign immu.privilege = privilege_level;
    assign dmmu.privilege = mstatus.mprv ? privilege_t'(mstatus.mpp) : privilege_level;
    assign immu.satp_ppn = satp.ppn;
    assign dmmu.satp_ppn = satp.ppn;
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //SEPC
    always_ff @(posedge clk) begin
        sepc[1:0] <= '0;
        if (rst)
            sepc[31:2] <= '0;
        else if (swrite_en(SEPC) | (exception_pkt.valid & exception_delegated) | (interrupt_taken & interrupt_delegated))
            sepc[31:2] <= (exception_pkt.valid | interrupt_taken) ? exception_pkt.pc[31:2] : updated_csr[31:2];
    end

    ////////////////////////////////////////////////////
    //SCAUSE
    always_ff @(posedge clk) begin
        scause.zeros <= '0;
        if (rst) begin
            scause.is_interrupt <= 0;
            scause.code <= '0;
        end
        else if ((swrite_en(SCAUSE) | (exception_pkt.valid & exception_delegated) | (interrupt_taken & interrupt_delegated))) begin
            scause.is_interrupt <= interrupt_taken | (swrite_en(SCAUSE) & updated_csr[31]);
            scause.code <= interrupt_taken ? interrupt_cause_r : exception_pkt.valid ? exception_pkt.code : updated_csr[ECODE_W-1:0];
        end
    end

    ////////////////////////////////////////////////////
    //STVEC
    always_ff @(posedge clk) begin
        stvec[1:0] <= '0;
        if (rst)
            stvec[31:2] <= CONFIG.CSRS.RESET_TVEC[31:2];
        else if (swrite_en(STVEC))
            stvec[31:2] <= updated_csr[31:2];
    end

    ////////////////////////////////////////////////////
    //STVAL
    always_ff @(posedge clk) begin
        if (rst)
            stval <= '0;
        else if (swrite_en(STVAL) | (exception_pkt.valid & exception_delegated))
            stval <= exception_pkt.valid ? exception_pkt.tval : updated_csr;
    end

    ////////////////////////////////////////////////////
    //SATP
    always_ff @(posedge clk) begin
        if (rst)
            satp <= 0;
        else if (swrite_en(SATP))
            satp <= updated_csr;
    end

    ////////////////////////////////////////////////////
    //SCOUNTEREN
    always_ff @(posedge clk) begin
        if (rst)
            scounteren <= 0;
        else if (swrite_en(SCOUNTEREN))
            scounteren <= updated_csr;
    end

    ////////////////////////////////////////////////////
    //SSCRATCH
    always_ff @(posedge clk) begin
        if (rst)
            sscratch <= '0;
        else if (swrite_en(SSCRATCH))
            sscratch <= updated_csr;
    end

    ////////////////////////////////////////////////////
    //SENVCFG
    localparam envcfg_t senvcfg_mask = '{default:0, fiom: 1, cbie:{2{CONFIG.INCLUDE_CBO}}, cbcfe:CONFIG.INCLUDE_CBO};
    always_ff @(posedge clk) begin
        if (rst)
            senvcfg <= '0;
        else if (swrite_en(SENVCFG) & CONFIG.MODES == MSU)
            senvcfg <= updated_csr & senvcfg_mask;
    end

    ////////////////////////////////////////////////////
    //STIMECMP
    always_ff @(posedge clk) begin
        if (rst) begin
            stimecmp <= '0;
            stimecmph <= '0;
        end
        else begin
            if (swrite_en(STIMECMP) & CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SSTC)
                stimecmp <= updated_csr;
            if (swrite_en(STIMECMPH) & CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SSTC)
                stimecmph <= updated_csr;
        end
    end

    assign stip_stimecmp = mtime >= {stimecmph, stimecmp};

    ////////////////////////////////////////////////////
    //SIP
    assign sip = mip & mideleg;

    ////////////////////////////////////////////////////
    //SIE
    assign sie_deleg_mask = sie_mask & mie_t'(mideleg);
    assign sie = mie & sie_deleg_mask;

    ////////////////////////////////////////////////////
    //SSTATUS
    assign sstatus = mstatus & sstatus_mask;

end
endgenerate

    ////////////////////////////////////////////////////
    //END OF SUPERVISOR REGS
    ////////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    //Timers and Counters
    //Register increment for instructions completed
    //Can be inhbited by mcountinhibit
    localparam COUNTER_W = 64;

    logic[COUNTER_W-1:0] mcycle;
    logic[COUNTER_W-1:0] minstret;

    logic[COUNTER_W-1:0] mcycle_input_next;
    logic mcycle_inc;
    logic pending_inst;
    logic increment_minstret;

    assign mcycle_input_next[31:0] = mwrite_en(MCYCLE) ? updated_csr : mcycle[31:0];
    assign mcycle_input_next[COUNTER_W-1:32] = mwrite_en(MCYCLEH) ? updated_csr[COUNTER_W-33:0] : mcycle[COUNTER_W-1:32];
    assign mcycle_inc = (CONFIG.MODES != BARE | CONFIG.CSRS.INCLUDE_ZICNTR) & ~((mwrite_en(MCYCLE) | mwrite_en(MCYCLEH))) & ~mcountinhibit.cy;

    always_ff @(posedge clk) begin
        if (rst) 
            mcycle <= 0;
        else
            mcycle <= mcycle_input_next + COUNTER_W'(mcycle_inc);
    end


    //Branch and pre issue exceptions retire the pending
    assign increment_minstret = pending_inst & (exception_pkt.valid ? exception_pkt.source[BR_EXCEPTION] | exception_pkt.source[PRE_ISSUE_EXCEPTION] : ~exception_pkt.possible);
    always_ff @(posedge clk) begin
        if (rst)
            pending_inst <= 0;
        else begin
            if (instruction_issued & ~mcountinhibit.ir)
                pending_inst <= 1;
            else if (mwrite_en(MINSTRET) | mwrite_en(MINSTRETH) | (~exception_pkt.possible | ~exception_pkt.valid))
                pending_inst <= 0;
        end
    end

    always_ff @(posedge clk) begin
        if (rst)
            minstret <= 0;
        else if ((CONFIG.MODES != BARE | CONFIG.CSRS.INCLUDE_ZICNTR) & increment_minstret)
            minstret <= minstret + 1;
    end

    ////////////////////////////////////////////////////
    //Floating-Point status register
    //Contains 5 exception flags (invalid, inexact, overflow, underflow, divide by zero)
    //Also contains dynamic rounding mode (round to zero, round to +infinity, round to -infinity, round to nearest ties to even, round to nearest ties away)
    //These fields can be accessed individually or simultaneously through different addresses
    logic[2:0] frm;
    logic[4:0] fflags;
    assign dyn_rm = frm;

generate if (CONFIG.INCLUDE_UNIT.FPU) begin : gen_csr_fp
    //Older versions of the spec mandated an illegal instruction exception if an instruction
    //with the dynamic rounding mode was issued and the frm register contained an invalid 
    //rounding mode. This has since been changed to "reserved" behaviour, meaning we do not 
    //have to do anything special. In this case, fp_roundup would default to rne

    always_ff @(posedge clk) begin
        if (rst) begin
            frm <= '0;
            fflags <= '0;
        end
        else begin
            //Explicit writes commit earlier than regular CSR writes because they are required by FP instructions
            case ({commit, csr_inputs_r.addr})
                {1'b1, FFLAGS} : fflags <= next_csr[4:0];
                {1'b1, FRM} : frm <= next_csr[2:0];
                {1'b1, FCSR} : {frm, fflags} <= next_csr[7:0];
                default : fflags <= fflags | fflag_wmask; //Implicit writes (can never overlap explicit writes)
            endcase
        end
    end
end endgenerate


    ////////////////////////////////////////////////////
    //GC Connections
    logic will_flush;
    always_ff @(posedge clk) begin
        if (issue.new_request)
            will_flush <= CONFIG.MODES == MSU & csr_inputs.writes & csr_inputs.addr inside {SATP, MSTATUS, SSTATUS};
        csr_frontend_flush <= commit & will_flush;
    end

    assign exception_target_pc = exception_delegated | interrupt_delegated ? stvec : mtvec;


    ////////////////////////////////////////////////////
    //Exceptions
    //Illegal instruction on wrong addresses, privilege
    //issues, and writing read only registers
generate if (CONFIG.MODES != BARE) begin : gen_csr_exceptions
    logic legal_access;

    always_comb begin
        case (csr_inputs.addr) inside
            FFLAGS, FRM, FCSR : legal_access = CONFIG.INCLUDE_UNIT.FPU; //FPU always accessible if present
            MVENDORID, MARCHID, MIMPID, MHARTID, MCONFIGPTR : legal_access = privilege_level == MACHINE_PRIVILEGE & ~csr_inputs.writes; //Read only
            MSTATUS, MISA, MIE, MTVEC, MSTATUSH, MSCRATCH, MEPC, MCAUSE, MTVAL, MIP, MCYCLE, MINSTRET, [MHPMCOUNTER3H:MHPMCOUNTER31], MCYCLEH, MINSTRETH, [MHPMCOUNTER3H:MHPMCOUNTER31H], MCOUNTINHIBIT, [MHPMEVENT3:MHPMEVENT31], [MHPMEVENT3H:MHPMEVENT31H] : legal_access = privilege_level == MACHINE_PRIVILEGE; //Read write
            MEDELEG, MIDELEG, MEDELEGH : legal_access = CONFIG.MODES == MSU & privilege_level == MACHINE_PRIVILEGE; //Read write, needs supervisor
            [MSTATEEN0:MSTATEEN3], [MSTATEEN0H:MSTATEEN3H] : legal_access = CONFIG.CSRS.INCLUDE_SMSTATEEN & privilege_level == MACHINE_PRIVILEGE; //Read write, needs extension
            MCOUNTEREN, MENVCFG, MENVCFGH : legal_access = CONFIG.MODES inside {MU, MSU} & privilege_level == MACHINE_PRIVILEGE; //Read write, needs user
            SSTATUS, SIE, STVEC, SCOUNTEREN, SSCRATCH, SEPC, SCAUSE, STVAL, SIP, SENVCFG : legal_access = CONFIG.MODES == MSU & privilege_level inside {MACHINE_PRIVILEGE, SUPERVISOR_PRIVILEGE}; //Read write
            SATP : legal_access = CONFIG.MODES == MSU & ((privilege_level == MACHINE_PRIVILEGE) | (privilege_level == SUPERVISOR_PRIVILEGE & ~mstatus.tvm)); //Read write, not TVM
            SENVCFG : legal_access = CONFIG.MODES == MSU & ((privilege_level == MACHINE_PRIVILEGE) | (privilege_level == SUPERVISOR_PRIVILEGE & (~CONFIG.CSRS.INCLUDE_SMSTATEEN | mstateen0h.envcfg))); //Read write, depends on mstateen0h
            SSTATEEN0 : legal_access = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SMSTATEEN & ((privilege_level == MACHINE_PRIVILEGE) | (privilege_level == SUPERVISOR_PRIVILEGE & mstateen0h.se0)); //Read write, needs extension and mstateen0h
            [SSTATEEN1:SSTATEEN3] : legal_access = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SMSTATEEN & privilege_level inside {MACHINE_PRIVILEGE, SUPERVISOR_PRIVILEGE}; //Read write, needs extension
            CYCLE, TIME, INSTRET, CYCLEH, TIMEH, INSTRETH : begin //Read only, depends on m/scounteren and extension
                legal_access = CONFIG.CSRS.INCLUDE_ZICNTR & ~csr_inputs.writes;
                if (privilege_level != MACHINE_PRIVILEGE)
                    legal_access &= mcounteren[csr_inputs.addr[4:0]];
                if (CONFIG.MODES == MSU & privilege_level == USER_PRIVILEGE)
                    legal_access &= scounteren[csr_inputs.addr[4:0]];
            end
            [HPMCOUNTER3:HPMCOUNTER31], [HPMCOUNTER3H:HPMCOUNTER31H] : begin //Read only, depends on m/scounteren and extension
                legal_access = CONFIG.CSRS.INCLUDE_ZIHPM & ~csr_inputs.writes;
                if (privilege_level != MACHINE_PRIVILEGE)
                    legal_access &= mcounteren[csr_inputs.addr[4:0]];
                if (CONFIG.MODES == MSU & privilege_level == USER_PRIVILEGE)
                    legal_access &= scounteren[csr_inputs.addr[4:0]];
            end
            STIMECMP, STIMECMPH : legal_access = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SSTC & ((privilege_level == MACHINE_PRIVILEGE) | (privilege_level == SUPERVISOR_PRIVILEGE & mcounteren.tm & menvcfgh.stce)); //Read write, depends on TM + STCE
            default: legal_access = 0;
        endcase
    end


    always_ff @(posedge clk) begin
        if (rst)
            illegal_instruction <= 0;
        else if (issue.new_request)
            illegal_instruction <= ~legal_access;
    end

    always_ff @(posedge clk) begin
        if (rst)
            exception.valid <= 0;
        else
            exception.valid <= commit & illegal_instruction;
    end

    assign exception.code = ILLEGAL_INST;
    assign exception.pc = issue_stage.pc_r;
    assign exception.tval = issue_stage.instruction_r;
    assign exception.discard = |issue_stage.instruction_r[11:7]; //Only discard if rd != x0

end
endgenerate

    //Interrupts need to be immediately evaluated folowing MRET/SRET or writing to a CSR that
    //controls interrupts. MRET/SRET flush the fetch pipeline so nothing needs to be done,
    //but we must stall for 1 cycle after writing certain CSRs to ensure pending_interrupt
    //can be raised and detected before another instruction is issued
    logic stall_for_interrupt;
    always_ff @(posedge clk) begin
        stall_for_interrupt <= wb.done & wb.ack & csr_inputs_r.writes & (mwrite_en(MIP) | mwrite_en(MIE) | mwrite_en(MSTATUS) | mwrite_en(MIDELEG) | swrite_en(SIP) | swrite_en(SIE) | swrite_en(SSTATUS));
    end

    assign exception.possible = busy | exception.valid | stall_for_interrupt; //Block future instructions

    ////////////////////////////////////////////////////
    //CSR mux
    always_comb begin
        case (csr_inputs_r.addr) inside
            //Floating point
            FFLAGS : selected_csr = CONFIG.INCLUDE_UNIT.FPU ? {27'b0, fflags} : '0;
            FRM : selected_csr = CONFIG.INCLUDE_UNIT.FPU ? {29'b0, frm} : '0;
            FCSR : selected_csr = CONFIG.INCLUDE_UNIT.FPU ? {24'b0, frm, fflags} : '0;

            //Machine info
            MVENDORID : selected_csr = CONFIG.MODES != BARE ? mvendorid : '0;
            MARCHID : selected_csr = CONFIG.MODES != BARE ? marchid : '0;
            MIMPID : selected_csr = CONFIG.MODES != BARE ? mimpid : '0;
            MHARTID : selected_csr = CONFIG.MODES != BARE ? mhartid : '0; 
            MCONFIGPTR : selected_csr = CONFIG.MODES != BARE ? mconfigptr : '0;
            //Machine trap setup
            MSTATUS : selected_csr = CONFIG.MODES != BARE ? mstatus : '0;
            MISA :  selected_csr = CONFIG.MODES != BARE ? misa : '0;
            MEDELEG : selected_csr = CONFIG.MODES == MSU ? medeleg : '0;
            MIDELEG : selected_csr = CONFIG.MODES == MSU ? mideleg : '0;
            MIE : selected_csr = CONFIG.MODES != BARE ? mie : '0;
            MTVEC : selected_csr = CONFIG.MODES != BARE ? mtvec : '0;
            MCOUNTEREN : selected_csr = CONFIG.MODES inside {MU, MSU} ? mcounteren : '0;
            MSTATUSH : selected_csr = CONFIG.MODES != BARE ? mstatush : '0;
            MEDELEGH : selected_csr = CONFIG.MODES == MSU ? medelegh : '0;
            //Machine trap handling
            MSCRATCH : selected_csr = CONFIG.MODES != BARE ? mscratch : '0;
            MEPC : selected_csr = CONFIG.MODES != BARE ? mepc : '0;
            MCAUSE : selected_csr = CONFIG.MODES != BARE ? mcause : '0;
            MTVAL : selected_csr = CONFIG.MODES != BARE ? mtval : '0;
            MIP : selected_csr = CONFIG.MODES != BARE ? mip : '0;
            //Machine configuration
            MENVCFG : selected_csr = CONFIG.MODES inside {MU, MSU} ? menvcfg : '0;
            MENVCFGH : selected_csr = CONFIG.MODES inside {MU, MSU} ? menvcfgh : '0;
            //No PMP
            //MHPM COUNTER
            //Machine Timers and Counters
            MCYCLE : selected_csr = CONFIG.MODES != BARE ? mcycle[31:0] : '0;
            MINSTRET : selected_csr = CONFIG.MODES != BARE ? minstret[31:0] : '0;
            [MHPMCOUNTER3 : MHPMCOUNTER31] : selected_csr = '0;
            MCYCLEH : selected_csr = CONFIG.MODES != BARE ? 32'(mcycle[COUNTER_W-1:32]) : '0;
            MINSTRETH : selected_csr = CONFIG.MODES != BARE ? 32'(minstret[COUNTER_W-1:32]) : '0;
            [MHPMCOUNTER3H : MHPMCOUNTER31H] : selected_csr = '0;
            //Machine Counter Setup
            MCOUNTINHIBIT : selected_csr = CONFIG.MODES != BARE ? mcountinhibit : '0;
            [MHPMEVENT3 : MHPMEVENT31] : selected_csr = '0;
            [MHPMEVENT3H : MHPMEVENT31H] : selected_csr = '0;
            //Machine state enable
            MSTATEEN0 : selected_csr = CONFIG.MODES != BARE & CONFIG.CSRS.INCLUDE_SMSTATEEN ? mstateen0 : '0;
            MSTATEEN1 : selected_csr = CONFIG.MODES != BARE & CONFIG.CSRS.INCLUDE_SMSTATEEN ? mstateen1 : '0;
            MSTATEEN2 : selected_csr = CONFIG.MODES != BARE & CONFIG.CSRS.INCLUDE_SMSTATEEN ? mstateen2 : '0;
            MSTATEEN3 : selected_csr = CONFIG.MODES != BARE & CONFIG.CSRS.INCLUDE_SMSTATEEN ? mstateen3 : '0;
            MSTATEEN0H : selected_csr = CONFIG.MODES != BARE & CONFIG.CSRS.INCLUDE_SMSTATEEN ? mstateen0h : '0;
            MSTATEEN1H : selected_csr = CONFIG.MODES != BARE & CONFIG.CSRS.INCLUDE_SMSTATEEN ? mstateen1h : '0;
            MSTATEEN2H : selected_csr = CONFIG.MODES != BARE & CONFIG.CSRS.INCLUDE_SMSTATEEN ? mstateen2h : '0;
            MSTATEEN3H : selected_csr = CONFIG.MODES != BARE & CONFIG.CSRS.INCLUDE_SMSTATEEN ? mstateen3h : '0;

            //Supervisor regs
            //Supervisor Trap Setup
            SSTATUS : selected_csr = CONFIG.MODES == MSU ? sstatus : '0;
            SIE : selected_csr = CONFIG.MODES == MSU ? sie : '0;
            STVEC : selected_csr = CONFIG.MODES == MSU ? stvec : '0;
            SCOUNTEREN : selected_csr = '0;
            //Supervisor configuration
            SENVCFG : selected_csr = CONFIG.MODES == MSU ? senvcfg : '0;
            //Supervisor trap handling
            SSCRATCH : selected_csr = CONFIG.MODES == MSU ? sscratch : '0;
            SEPC : selected_csr = CONFIG.MODES == MSU ? sepc : '0;
            SCAUSE : selected_csr = CONFIG.MODES == MSU ? scause : '0;
            STVAL : selected_csr = CONFIG.MODES == MSU ? stval : '0;
            SIP : selected_csr = CONFIG.MODES == MSU ? sip : '0;
            STIMECMP : selected_csr = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SSTC ? stimecmp : '0;
            STIMECMPH : selected_csr = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SSTC ? stimecmph : '0;
            //Supervisor address translation and protection
            SATP : selected_csr = CONFIG.MODES == MSU ? satp : '0;
            //Supervisor state enable
            SSTATEEN0 : selected_csr = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SMSTATEEN ? sstateen0 : '0;
            SSTATEEN1 : selected_csr = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SMSTATEEN ? sstateen1 : '0;
            SSTATEEN2 : selected_csr = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SMSTATEEN ? sstateen2 : '0;
            SSTATEEN3 : selected_csr = CONFIG.MODES == MSU & CONFIG.CSRS.INCLUDE_SMSTATEEN ? sstateen3 : '0;

            //Timers and counters
            CYCLE : selected_csr = CONFIG.CSRS.INCLUDE_ZICNTR ? mcycle[31:0] : '0;
            TIME : selected_csr = CONFIG.CSRS.INCLUDE_ZICNTR ? mtime[31:0] : '0;
            INSTRET : selected_csr = CONFIG.CSRS.INCLUDE_ZICNTR ? minstret[31:0] : '0;
            [HPMCOUNTER3 : HPMCOUNTER31] : selected_csr = '0;
            CYCLEH : selected_csr = CONFIG.CSRS.INCLUDE_ZICNTR ? 32'(mcycle[COUNTER_W-1:32]) : '0;
            TIMEH : selected_csr = CONFIG.CSRS.INCLUDE_ZICNTR ? mtime[63:32] : '0;
            INSTRETH : selected_csr = CONFIG.CSRS.INCLUDE_ZICNTR ? 32'(minstret[COUNTER_W-1:32]) : '0;
            [HPMCOUNTER3H : HPMCOUNTER31H] : selected_csr = '0;

            default : selected_csr = '0;
        endcase
    end
    always_ff @(posedge clk) begin
        if (commit)
            selected_csr_r <= selected_csr;
    end

    ////////////////////////////////////////////////////
    //Assertions
    mstatus_update_assertion:
        assert property (@(posedge clk) disable iff (rst) $onehot0({mret,sret,interrupt_taken, exception_pkt.valid,(mwrite_en(MSTATUS) | swrite_en(SSTATUS))})) else $error("multiple write to mstatus");

endmodule
