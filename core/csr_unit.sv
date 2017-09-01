/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */
 
import taiga_config::*;
import taiga_types::*;

module csr_unit (
        input logic clk,
        input logic rst,
        func_unit_ex_interface.unit csr_ex,
        unit_writeback_interface.unit csr_wb, //        writeback_unit_interface_dummy.unit csr_wb, //        writeback_unit_interface_dummy.unit csr_wb,

        //Decode
        csr_inputs_interface.unit csr_inputs,
        input logic instruction_issued_no_rd,

        //exception_control
        csr_exception_interface.csr csr_exception,

        //TLBs
        output logic tlb_on,
        output logic [9:0] asid,

        //MMUs
        mmu_interface.csr immu,
        mmu_interface.csr dmmu,

        //WB
        input logic instruction_complete,

        input logic return_from_exception,

        //External
        input logic interrupt

        );

    typedef struct packed {
        logic [2:0] rw_bits;
        logic [2:0] privilege;
        logic [7:0] sub_addr;
    } csr_addr_t;

    //Constant registers
    typedef struct packed {
        logic[1:0] base; //RV32I
        logic[2:0] reserved;
        logic Z;
        logic Y;
        logic X;
        logic W;
        logic V;
        logic U; //User mode
        logic T;
        logic S; //Supervisor mode
        logic R;
        logic Q;
        logic P;
        logic O;
        logic N;
        logic M; //multiply divide
        logic L;
        logic K;
        logic J;
        logic I; //Base
        logic H;
        logic G;
        logic F;
        logic E;
        logic D;
        logic C;
        logic B;
        logic A; //Atomic
    } misa_t;

    misa_t misa;

    bit [XLEN-1:0] mvendorid = 0;
    bit [XLEN-1:0] marchid = 0;
    bit [XLEN-1:0] mimpid = 0;
    bit [XLEN-1:0] mhartid = CPU_ID;


    typedef struct packed {
        logic  sd;
        logic [XLEN-2:29] zero_bits1;
        logic [4:0] vm;
        logic [23:20] zero_bits2;
        logic mxr;
        logic pum;
        logic mprv;
        logic [1:0] xs;
        logic [1:0] fs;
        logic [1:0] mpp;
        logic [1:0] hpp;
        logic spp;
        logic mpie;
        logic hpie;
        logic spie;
        logic upie;
        logic mie;
        logic hie;
        logic sie;
        logic uie;
    } mstatus_t;

    mstatus_t mstatus, mstatus_write, mstatus_exception, mstatus_return, mstatus_next, mstatus_mask, mstatus_mmask, mstatus_smask;


    typedef struct packed {
        logic [XLEN-1:12] zeros;
        logic meip;
        logic heip;
        logic seip;
        logic ueip;
        logic mtip;
        logic htip;
        logic stip;
        logic utip;
        logic msip;
        logic hsip;
        logic ssip;
        logic usip;
    } mip_t;

    typedef struct packed {
        logic [XLEN-1:12] zeros;
        logic meie;
        logic heie;
        logic seie;
        logic ueie;
        logic mtie;
        logic htie;
        logic stie;
        logic utie;
        logic msie;
        logic hsie;
        logic ssie;
        logic usie;
    } mie_t;

    struct packed {
        logic [9:0] asid;
        logic [21:0] ppn;
    } sptbr;

    //Non-constant registers

    //scratch ram
    logic[XLEN-1:0] scratch_regs [15:0];//Only 0x1 and 0x3 used by supervisor and machine mode respectively
    logic[XLEN-1:0] scratch_out;


    logic[XLEN-1:0] mtvec;
    logic[XLEN-1:0] medeleg;
    logic[XLEN-1:0] mideleg;
    mip_t mip, mip_mask;
    mie_t mie_reg, mie_mask;
    logic[XLEN-1:0] mepc;

    logic[XLEN-1:0] mtimecmp;

    logic[XLEN-1:0] mcause;
    logic[XLEN-1:0] mbadaddr;

    mip_t sip_mask;
    mie_t sie_mask;
    logic[XLEN-1:0] sepc;

    logic[XLEN-1:0] stime;
    logic[XLEN-1:0] stimecmp;

    logic[XLEN-1:0] scause;
    logic[XLEN-1:0] sbadaddr;

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

    logic msr_write;
    logic msr_update;


    logic [1:0] privilege_level;
    logic [1:0] next_privilege_level;

    logic [31:0] selected_csr;
    logic [31:0] updated_csr;

    logic invalid_addr;

    logic machine_trap;
    logic supervisor_trap;

    //******************************************************************

    //TLB status --- used to mux physical/virtual address
    assign tlb_on = mstatus.vm[3]; //We only support Sv32 or Mbare so only need to check one bit
    assign asid = sptbr.asid;
    //******************

    //MMU interface
    assign immu.mxr = mstatus.mxr;
    assign dmmu.mxr = mstatus.mxr;
    assign immu.pum = mstatus.pum;
    assign dmmu.pum = mstatus.pum;
    assign immu.privilege = privilege_level;
    assign dmmu.privilege = mstatus.mprv ? mstatus.mpp : privilege_level;
    assign immu.ppn = sptbr.ppn;
    assign dmmu.ppn = sptbr.ppn;
    //******************

    //Machine ISA register
    assign misa = '{default:0, base:1, U:1, S:1, M:1, I:1};


    //assign exception = interrupt | misaligned_fetch | instruction_fault | illegal_opcode | unaligned_load | unaligned_store | load_fault | store_fault;

    //convert addr into packed struct form
    assign  csr_addr = csr_inputs.csr_addr;
    assign privilege_exception = csr_ex.new_request  && (csr_addr.privilege > privilege_level);

    assign user_write = !csr_inputs.system_op && !privilege_exception && (csr_addr.rw_bits != CSR_READ_ONLY && csr_addr.privilege == USER);
    assign supervisor_write = !csr_inputs.system_op && !privilege_exception && (csr_addr.rw_bits != CSR_READ_ONLY && csr_addr.privilege == SUPERVISOR);
    assign machine_write = !csr_inputs.system_op && !privilege_exception && (csr_addr.rw_bits != CSR_READ_ONLY && csr_addr.privilege == MACHINE);

    assign csr_exception.illegal_instruction = invalid_addr | privilege_exception;

    assign machine_trap = csr_exception.valid && next_privilege_level == MACHINE;
    assign supervisor_trap = csr_exception.valid && next_privilege_level == SUPERVISOR;

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


    assign csr_wb.early_done = csr_ex.new_request | (csr_wb.done & ~csr_wb.accepted);

    always_ff @(posedge clk) begin
        if (rst) begin
            csr_wb.done <= 0;
        end else if (csr_ex.new_request) begin
            csr_wb.done <= 1;
        end else if (csr_wb.accepted) begin
            csr_wb.done <= 0;
        end
    end

    always_comb begin
        case (csr_inputs.csr_op)
            //  CSR_RW : updated_csr = csr_inputs.rs1;
            CSR_RS : updated_csr = selected_csr | csr_inputs.rs1;
            CSR_RC : updated_csr = selected_csr & ~csr_inputs.rs1;
            default : updated_csr = csr_inputs.rs1;//selected_csr;
        endcase
    end

    //In progress---------------------------
//    always_comb begin
//        next_privilege_level = MACHINE;
//        if (interrupt) begin
//            next_privilege_level = MACHINE;
//        end
//        else if (csr_exception.valid) begin
//            if (medeleg[csr_exception.code])
//                next_privilege_level = SUPERVISOR;
//        end
//        else if (return_from_exception) begin
//            next_privilege_level = USER;
//        end
//    end
//    //Current privilege level
//    always_ff @(posedge clk) begin
//        if (rst) begin
//            privilege_level <= MACHINE;
//        end else if (csr_exception.valid | return_from_exception) begin
//            privilege_level <= next_privilege_level;
//        end
//    end

//    //save previous interrupt and privilege info on exception
//    always_comb begin
//        mstatus_exception = mstatus;
//        unique case (next_privilege_level)
//            SUPERVISOR: begin
//                mstatus_exception.spie = (privilege_level == SUPERVISOR) ? mstatus.sie : mstatus.uie;
//                mstatus_exception.sie = 0;
//                mstatus_exception.spp = privilege_level[0]; //one if from supervisor-mode, zero if from user-mode
//            end
//            MACHINE: begin
//                mstatus_exception.mpie = (privilege_level == MACHINE) ? mstatus.mie : ((privilege_level == SUPERVISOR) ? mstatus.sie : mstatus.uie);
//                mstatus_exception.mie = 0;
//                mstatus_exception.mpp = privilege_level; //machine,supervisor or user
//            end
//        endcase
//    end

//    //return from trap
//    always_comb begin
//        mstatus_return = mstatus;
//        unique case (next_privilege_level)
//            SUPERVISOR: begin
//                if (mstatus.spp) begin //supervisor
//                    mstatus_return.sie = mstatus.spie;
//                    mstatus_return.spie = 1;
//                    mstatus_return.spp = 0;
//                end
//                else begin //user
//                    mstatus_return.spie = 1;
//                    mstatus_return.spp = 0;
//                end
//            end
//            MACHINE: begin
//                unique case(mstatus.mpp)
//                    USER: begin
//                        mstatus_return.mpie = 1;
//                        mstatus_return.mpp = USER;
//                    end
//                    SUPERVISOR: begin
//                        mstatus_return.sie = mstatus.mpie;
//                        mstatus_return.mpie = 1;
//                        mstatus_return.mpp = USER;
//                    end
//                    MACHINE: begin
//                        mstatus_return.mie = mstatus.mpie;
//                        mstatus_return.mpie = 1;
//                        mstatus_return.mpp = USER;
//                    end
//                endcase
//            end
//        endcase
//    end

//    //machine status mask
//    assign mstatus_mmask = '{default:0, vm:SV32, mxr:1, pum:1, mprv:1, mpp:'1, spp:1, mpie:1, spie:1, mie:1, sie:1};
//    //supervisor status mask
//    assign mstatus_smask  = '{default:0, pum:1, spp:1, spie:1, sie:1};

//    assign mstatus_mask = machine_write ? mstatus_mmask : mstatus_smask;

//    assign mstatus_write = (mstatus & ~mstatus_mask) | (updated_csr & mstatus_mask);
//    assign msr_write = (machine_write && csr_addr.sub_addr == MSTATUS[7:0]) | (supervisor_write && csr_addr.sub_addr == SSTATUS[7:0]);


//    //read_write portion of machine status register
//    always_ff @(posedge clk) begin
//        if (rst) begin
//            mstatus. vm <= BARE;
//            mstatus.mxr <= 0;
//            mstatus.pum <= 0;
//            mstatus.mprv <= 0;
//            mstatus.mpp <= MACHINE;
//            mstatus.spp <= 0;
//            mstatus.mpie <= 0;
//            mstatus.spie <= 0;
//            mstatus.mie <= 0;
//            mstatus.sie <= 0;
//            //*****************
//            // Constant zeros
//            //*****************
//            //No FPU or custom extensions with state
//            mstatus.sd <= 0;
//            mstatus. zero_bits1 <= 0;
//            mstatus. zero_bits2 <= 0;
//            mstatus.xs <= 0;
//            mstatus.fs <= 0;
//            //No hypervisor
//            mstatus.hpp <= 0;
//            mstatus.hpie <= 0;
//            mstatus.hie <= 0;
//            //No user mode interrupts
//            mstatus.upie <= 0;
//            mstatus.uie <= 0;
//        end
//        else if (csr_exception.valid)
//            mstatus <= mstatus_exception;
//        else if (return_from_exception)
//            mstatus <= mstatus_return;
//        else if (msr_write)
//            mstatus <= mstatus_write;
//    end



//    //mtvec
//    always_ff @(posedge clk) begin
//        if (rst) begin
//            mtvec <= {RESET_VEC[XLEN-1:2], 2'b00};
//        end else if (machine_write && csr_addr.sub_addr == MTVEC[7:0]) begin
//            mtvec <= {updated_csr[XLEN-1:2], 2'b00};
//        end
//    end

//    //medeleg
//    //assign medeleg_mask = '{default:0, seip:1, stip:1, ssip:1};
//    always_ff @(posedge clk) begin
//        if (rst) begin
//            medeleg <= '0;
//        end else if (machine_write && csr_addr.sub_addr == MEDELEG[7:0]) begin
//            medeleg <= updated_csr;
//        end
//    end

//    //mideleg
//    always_ff @(posedge clk) begin
//        if (rst) begin
//            mideleg <= '0;
//        end else if (machine_write && csr_addr.sub_addr == MIDELEG[7:0]) begin
//            // mideleg <= (mideleg & ~mideleg_mask) | (updated_csr & mideleg_mask);
//        end
//    end

//    //mip
//    assign mip_mask = '{default:0, stip:1, ssip:1};
//    always_ff @(posedge clk) begin
//        if (rst) begin
//            mip <= 0;
//        end
//        else if (machine_write && csr_addr.sub_addr == MIP[7:0]) begin
//            mip <= (mip & ~mip_mask) | (updated_csr & mip_mask);
//        end
//    end

//    //mie
//    assign mie_mask = '{default:0, meie:1, seie:1, mtie:1, stie:1, msie:1, ssie:1};
//    assign sie_mask = '{default:0, seie:1, stie:1, ssie:1};

//    always_ff @(posedge clk) begin
//        if (rst) begin
//            mie_reg <= '0;
//        end
//        else if (machine_write && csr_addr.sub_addr == MIE[7:0]) begin
//            mie_reg <= (mie_reg & ~mie_mask) | (updated_csr & mie_mask);
//        end
//        else if (supervisor_write && csr_addr.sub_addr == SIE[7:0]) begin
//            mie_reg <= (mie_reg & ~sie_mask) | (updated_csr & sie_mask);
//        end
//    end



//    //mtimecmp
//    // always_ff @(posedge clk) begin
//    //    if (rst) begin
//    //       mtimecmp <= '0;
//    //    end else if (machine_write && csr_addr.sub_addr == MTIMECMP[7:0]) begin
//    //       mtimecmp <= updated_csr;
//    //    end
//    //end


//    //mepc
//    always_ff @(posedge clk) begin
//        if (machine_trap) begin
//            mepc <= csr_exception.pc;
//        end
//        else if (machine_write && csr_addr.sub_addr == MEPC[7:0]) begin
//            mepc <= {updated_csr[XLEN-1:2], 2'b00};
//        end
//    end

//    //mcause
//    assign mcause[XLEN-1:ECODE_W] = 0;
//    always_ff @(posedge clk) begin
//        if (machine_trap) begin
//            mcause[ECODE_W-1:0] = csr_exception.code;
//        end
//        else if (machine_write && csr_addr.sub_addr == MCAUSE[7:0]) begin
//            mcause[ECODE_W-1:0] <= updated_csr[ECODE_W-1:0];
//        end
//    end

//    //mbadaddr
//    always_ff @(posedge clk) begin
//        if (machine_trap) begin
//            mbadaddr <= csr_exception.addr;
//        end
//        else if (machine_write && csr_addr.sub_addr == MBADADDR[7:0]) begin
//            mbadaddr <= updated_csr;
//        end
//    end

//    //END OF MACHINE REGS

//    //scratch regs
//    always_ff @(posedge clk) begin
//        if ((machine_write && csr_addr.sub_addr == MSCRATCH[7:0]) || (supervisor_write && csr_addr.sub_addr == SSCRATCH[7:0])) begin
//            scratch_regs[csr_addr.privilege] <= updated_csr;
//        end
//    end
//    assign scratch_out = scratch_regs[csr_addr.privilege];

//    //BEGIN OF SUPERVISOR REGS

//    assign sip_mask =  '{default:0, seip:1, stip:1, ssip:1};

//    //sepc
//    always_ff @(posedge clk) begin
//        if (supervisor_trap) begin
//            sepc <= csr_exception.pc;
//        end
//        else if (supervisor_write && csr_addr.sub_addr == SEPC[7:0]) begin
//            sepc <= updated_csr;
//        end
//    end

//    //scause
//    assign scause[XLEN-1:ECODE_W] = 0;
//    always_ff @(posedge clk) begin
//        if (supervisor_trap) begin
//            scause[ECODE_W-1:0] = csr_exception.code;
//        end
//        else if (supervisor_write && csr_addr.sub_addr == SCAUSE[7:0]) begin
//            scause[ECODE_W-1:0] <= updated_csr[ECODE_W-1:0];
//        end
//    end

//    //sbadaddr
//    always_ff @(posedge clk) begin
//        if (supervisor_trap) begin
//            sbadaddr <= csr_exception.addr;
//        end
//        else if (supervisor_write && csr_addr.sub_addr == SBADADDR[7:0]) begin
//            sbadaddr <= updated_csr;
//        end
//    end

//    //sptbr
//    always_ff @(posedge clk) begin
//        if (rst) begin
//            sptbr <= 0;
//        end else if (supervisor_write && csr_addr.sub_addr == SPTBR[7:0]) begin
//            sptbr <= updated_csr;
//        end
//    end

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
            MEPC : selected_csr = mepc;
            MCAUSE : selected_csr = mcause;
            MBADADDR : selected_csr = mbadaddr;
            MIP : selected_csr = mip;
                //Machine Timers and Counters
            MCYCLE : selected_csr = mcycle[XLEN-1:0];
            MTIME : selected_csr = mtime[XLEN-1:0];
            MINSTRET : selected_csr = minst_ret[XLEN-1:0];
            MCYCLEH : selected_csr = mcycle[TIMER_W-1:XLEN];
            MTIMEH : selected_csr = mtime[TIMER_W-1:XLEN];
            MINSTRETH : selected_csr = minst_ret[TIMER_W-1:XLEN];
                //Counter enables
            MUCOUNTEREN : selected_csr = 0;
            MSCOUNTEREN : selected_csr = 0;
                //counter deltas
            MUCYCLE_DELTA : selected_csr = 0;
            MUTIME_DELTA : selected_csr = 0;
            MUINSTRET_DELTA : selected_csr = 0;
            MSCYCLE_DELTA : selected_csr = 0;
            MSTIME_DELTA : selected_csr = 0;
            MSINSTRET_DELTA : selected_csr = 0;
            MUCYCLE_DELTAH : selected_csr = 0;
            MUTIME_DELTAH : selected_csr = 0;
            MUINSTRET_DELTAH : selected_csr = 0;
            MSCYCLE_DELTAH : selected_csr = 0;
            MSTIME_DELTAH : selected_csr = 0;
            MSINSTRET_DELTAH : selected_csr = 0;
                //Supervisor Trap Setup
            SSTATUS : selected_csr = (mstatus & mstatus_smask);
            SEDELEG : selected_csr = 0;
            SIDELEG : selected_csr = 0;
            SIE : selected_csr = (mie_reg & sie_mask);
            STVEC : selected_csr = stvec;
                //Supervisor trap handling
            SSCRATCH : selected_csr = scratch_out;
            SEPC : selected_csr = sepc;
            SCAUSE : selected_csr = scause;
            SBADADDR : selected_csr = sbadaddr;
            SIP : selected_csr = (mip & sip_mask);
                //Supervisor Protection and Translation
            SPTBR : selected_csr = sptbr;
                //Supervisor user shadows
            SCYCLE : selected_csr = mcycle[XLEN-1:0];
            STIME : selected_csr = mtime[XLEN-1:0];
            SINSTRET : selected_csr = minst_ret[XLEN-1:0];
            SCYCLEH : selected_csr = mcycle[TIMER_W-1:XLEN];
            STIMEH : selected_csr = mtime[TIMER_W-1:XLEN];
            SINSTRETH : selected_csr = minst_ret[TIMER_W-1:XLEN];

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


endmodule
