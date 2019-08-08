/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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

module gc_unit(
        input logic clk,
        input logic rst,


        //Decode
        func_unit_ex_interface.unit gc_ex,
        input gc_inputs_t gc_inputs,
        input logic instruction_issued_no_rd,

        //Branch miss predict
        input logic branch_flush,

        //Load Store Unit
        input exception_packet_t ls_exception,
        input logic ls_exception_valid,
        input logic load_store_issue,
        input logic load_store_FIFO_emptying,

        //TLBs
        output logic tlb_on,
        output logic [ASIDLEN-1:0] asid,

        //MMUs
        mmu_interface.csr immu,
        mmu_interface.csr dmmu,

        //WB
        input logic instruction_complete,
        input logic instruction_queue_empty,
        input instruction_id_t oldest_id,
        unit_writeback_interface.unit gc_wb,

        //External
        input logic interrupt,
        input logic timer_interrupt,

        //Output controls
        output logic gc_issue_hold,
        output logic gc_issue_flush,
        output logic gc_fetch_flush,
        output logic gc_fetch_pc_override,
        output logic gc_supress_writeback,

        output logic inorder,
        output logic inuse_clear,

        output logic [31:0] gc_fetch_pc
        );

    //Largest depth for TLBs
    localparam int TLB_CLEAR_DEPTH = (DTLB_DEPTH > ITLB_DEPTH) ? DTLB_DEPTH : ITLB_DEPTH;
    //For general reset clear, greater of TLB depth or inuse memory block (32-bits)
    localparam int CLEAR_DEPTH = ENABLE_S_MODE ? TLB_CLEAR_DEPTH : 32;

    logic [CLEAR_DEPTH-1:0] clear_shift_count;
    logic [TLB_CLEAR_DEPTH-1:0] tlb_clear_shift_count;
    ////////////////////////////////////////////////////
    enum {OP_ECALL, OP_EBREAK, OP_SRET, OP_MRET, OP_SFENCE, OP_FENCE, OP_FENCEI} operation;

    //Instructions
    //All instructions are processed only if in IDLE state, meaning there can be no exceptions caused by instructions already further in the pipeline.
    //FENCE:
    //    Drain Load/Store FIFO (i.e. not in in-order mode)
    //FENCE.I:
    //    flush and hold fetch until L/S unit empty
    //    Local mem (nothing extra required for coherency)
    //    Caches, currently not supported.  Need snooping for Icache and draining of data FIFO to L2 and after FIFO drained, poping at least the current number of entries in the invalidation FIFO
    //SFENCE
    //    flush and hold fetch, wait until L/S input FIFO empty, hold fetch until TLB update complete
    //ECALL, EBREAK, SRET, MRET:
    //    flush fetch, update CSRs (could be illegal instruction exception as well)

    //Interrupt
    //Hold issue, wait until IDLE state, flush fetch, take exception

    //Fetch Exception
    //flush fetch, wait until IDLE state, take exception.  If decode stage or later exception occurs first, exception is overridden

    //Illegal opcode (decode stage)
    //fetch flush, issue hold, wait until IDLE state, take exception.  If execute or later exception occurs first, exception is overridden

    //CSR exceptions
    //fetch flush, issue hold, capture ID/rd_non_zero and drain instruction queue, take exception.

    //LS exceptions (miss-aligned, TLB and MMU)
    //fetch flush, issue hold, capture ID/rd_non_zero and drain instruction queue, take exception.

    //Instruction queue drain:
    //  Two possibilities:
    //      1. Instruction stores to reg file.  ID in instruction queue, wait until that ID is oldest (either find oldest valid, or for small cycle penalty just look at last entry and wait for ID and valid)
    //      2. Instruction does not store to reg file.  If IQ not empty, wait for previously issued ID to complete, if empty no waiting required.
    //
    //      After all preceding instructions have been committed, continue popping instructions from queue but supress write-back operation until queue is drained.

    //In-order mode:
    //  Turn on when an instruction in the execute phase could cause an interrupt (L/S or CSR)
    //  Turn off when exception can no-longer occur (after one cycle for CSR, when L/S input FIFO will be empty)

    //*Complete issued instructions before exception
    //*Drain L/S FIFO then Hold fetch/issue during TLB clear
    //*Hold fetch until all stores committed
    //*Turn on inorder mode when L/S issued, turn off when no instruction can cause interrupt
    //     *If in-order mode and inflight queue empty, disable zero cycle write-back (eg. ALU)
    //*Hold fetch during potential fetch exception, when fetch buffer drained, if no other exceptions trigger exception

    typedef enum {RST_STATE, PRE_CLEAR_STATE, CLEAR_STATE, IDLE_STATE, TLB_CLEAR_STATE, LS_EXCEPTION_POSSIBLE, IQ_DRAIN, IQ_DISCARD} gc_state;
    gc_state state;
    gc_state next_state;

    logic i_fence_flush;
    exception_code_t ecall_code;

    //CSR
    logic mret;
    logic sret;
    logic [XLEN-1:0] selected_csr;
    csr_inputs_t csr_inputs;
    exception_packet_t gc_exception;
    exception_packet_t csr_exception;
    logic [1:0] current_privilege;
    logic [31:0] trap_pc;
    logic [31:0] csr_mepc;
    logic [31:0] csr_sepc;

    //Write-back handshaking
    logic processing;
    logic wb_done;

    logic [2:0] fn3;
    logic [6:0] opcode;
    logic [4:0] opcode_trim;

    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] future_rd_addr;

    //implementation
    ////////////////////////////////////////////////////


    //Instruction decode
    assign opcode = gc_inputs.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn3 = gc_inputs.instruction[14:12];
    assign rs1_addr = gc_inputs.instruction[19:15];

    always @(posedge clk) begin
        if (rst)
            state <= RST_STATE;
        else
            state <= next_state;
    end

    always_comb begin
        next_state = state;
        case (state)
            RST_STATE : next_state = PRE_CLEAR_STATE;
            PRE_CLEAR_STATE : next_state = CLEAR_STATE;
            CLEAR_STATE : if (clear_shift_count[CLEAR_DEPTH-1]) next_state = IDLE_STATE;
            IDLE_STATE : if (load_store_issue) next_state = LS_EXCEPTION_POSSIBLE;
            TLB_CLEAR_STATE : if (tlb_clear_shift_count[TLB_CLEAR_DEPTH-1]) next_state = IDLE_STATE;
            LS_EXCEPTION_POSSIBLE :
                if (load_store_FIFO_emptying)
                    next_state = IDLE_STATE;
                else if (ls_exception_valid) begin
                    if (ls_exception.id == oldest_id)
                        next_state = IQ_DISCARD;
                    else
                        next_state = IQ_DRAIN;
                end
            IQ_DRAIN :
                if (ls_exception.id == oldest_id)
                    next_state = IQ_DISCARD;
            IQ_DISCARD :
                if (instruction_queue_empty)
                    next_state = IDLE_STATE;
            default : next_state = RST_STATE;
        endcase
    end

    logic ls_exception_first_cycle;
    logic ls_exception_second_cycle;

    assign ls_exception_first_cycle =  ls_exception_valid && (state == LS_EXCEPTION_POSSIBLE);
    always_ff @ (posedge clk) begin
        ls_exception_second_cycle <= ls_exception_first_cycle;
    end

    assign gc_exception.code =
        ls_exception_second_cycle ? ls_exception.code :
        gc_inputs.is_ecall ? ecall_code : BREAK;
    assign gc_exception.pc = ls_exception_second_cycle ? ls_exception.pc : gc_inputs.pc;
    assign gc_exception.tval = ls_exception_second_cycle ? ls_exception.tval : '0;
    assign gc_exception.valid = gc_inputs.is_ecall | gc_inputs.is_ebreak | ls_exception_second_cycle;


    assign gc_fetch_flush = branch_flush | gc_inputs.flush_required | ls_exception_first_cycle;

    always_ff @ (posedge clk) begin
        gc_issue_hold <= gc_ex.new_request_dec || processing || (next_state inside {PRE_CLEAR_STATE, CLEAR_STATE, TLB_CLEAR_STATE, IQ_DRAIN, IQ_DISCARD});
        inuse_clear <= (next_state == CLEAR_STATE);
        inorder <= 0;//(next_state inside {LS_EXCEPTION_POSSIBLE, IQ_DRAIN});
    end

    always_ff @ (posedge clk) begin
        gc_issue_flush <= (next_state == IQ_DISCARD);
    end

    always_ff @ (posedge clk) begin
        gc_supress_writeback <= next_state inside {PRE_CLEAR_STATE, CLEAR_STATE, TLB_CLEAR_STATE, IQ_DISCARD} ? 1 : 0;
    end


    always_ff @ (posedge clk) begin
        gc_fetch_pc_override <= gc_inputs.flush_required | ls_exception_first_cycle;
        gc_fetch_pc <=
            gc_inputs.is_i_fence ? gc_inputs.pc + 4 :
            gc_inputs.is_ret ? csr_mepc :
            trap_pc;
    end

    //CLEAR state shift reg
    always_ff @ (posedge clk) begin
        clear_shift_count[0] <= (state == PRE_CLEAR_STATE) && (next_state == CLEAR_STATE);
        clear_shift_count[CLEAR_DEPTH-1:1] <= clear_shift_count[CLEAR_DEPTH-2:0];
    end
    //TLB_CLEAR state shift reg
    always_ff @ (posedge clk) begin
        tlb_clear_shift_count[0] <= (state == IDLE_STATE) && (next_state == TLB_CLEAR_STATE);
        tlb_clear_shift_count[TLB_CLEAR_DEPTH-1:1] <= tlb_clear_shift_count[TLB_CLEAR_DEPTH-2:0];
    end

    ////////////////////////////////////////////////////
    //CSR registers
    assign csr_inputs.rs1 = fn3[2] ? {27'b0, rs1_addr} : gc_inputs.rs1;
    assign csr_inputs.csr_addr = gc_inputs.instruction[31:20];
    assign csr_inputs.csr_op = fn3[1:0];
    assign csr_inputs.rs1_is_zero = (rs1_addr == 0);
    assign csr_inputs.rd_is_zero = gc_inputs.rd_is_zero;

    always_comb begin
        case (current_privilege)
            USER_PRIVILEGE : ecall_code = ECALL_U;
            SUPERVISOR_PRIVILEGE : ecall_code = ECALL_S;
            MACHINE_PRIVILEGE : ecall_code = ECALL_M;
            default : ecall_code = ECALL_U;
        endcase
    end

    csr_regs csr_registers (.*, .new_request(gc_inputs.is_csr & gc_ex.new_request));

    ////////////////////////////////////////////////////
    //Decode / Write-back Handshaking
    always_ff @(posedge clk) begin
        if (rst)
            processing <= 0;
        else if (gc_ex.new_request_dec)
            processing <= 1;
        else if (state == IDLE_STATE && instruction_queue_empty && (~wb_done | (wb_done & gc_wb.accepted )))
            processing <= 0;
    end

    assign gc_ex.ready = (state == IDLE_STATE) & ~processing;

    always_ff @(posedge clk) begin
        if (gc_ex.new_request) begin
            gc_wb.rd <= selected_csr;
        end
    end


    //Write_back
    assign gc_wb.done_next_cycle = gc_ex.new_request & gc_inputs.is_csr;
    always_ff @(posedge clk) begin
        gc_wb.instruction_id <= gc_ex.instruction_id;
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            wb_done <= 0;
        end else if (gc_ex.new_request & gc_inputs.is_csr) begin
            wb_done <= 1;
        end else if (gc_wb.accepted) begin
            wb_done <= 0;
        end
    end

    ////////////////////////////////////////////////////
    //Assertions
    always_ff @ (posedge clk) begin
        assert (~gc_wb.accepted | (gc_wb.accepted & wb_done)) else $error("Spurious ack for CSR Unit");
    end
    ////////////////////////////////////////////////////

endmodule
