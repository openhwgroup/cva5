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
        unit_issue_interface.unit issue,
        input gc_inputs_t gc_inputs,
        input logic instruction_issued_no_rd,
        input logic gc_flush_required,
        //Branch miss predict
        input logic branch_flush,

        //Load Store Unit
        input exception_packet_t ls_exception,
        input logic ls_exception_valid,

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
        //unit_writeback_interface.unit gc_wb,

        //External
        input logic interrupt,
        input logic timer_interrupt,

        //Output controls
        output logic gc_issue_hold,
        output logic gc_issue_flush,
        output logic gc_fetch_flush,
        output logic gc_fetch_pc_override,
        output logic gc_supress_writeback,

        output logic [31:0] gc_fetch_pc,

        //Write-back to Load-Store Unit
        output logic[31:0] csr_rd,
        output instruction_id_t csr_id,
        output logic csr_done
        );

    //Largest depth for TLBs
    localparam int TLB_CLEAR_DEPTH = (DTLB_DEPTH > ITLB_DEPTH) ? DTLB_DEPTH : ITLB_DEPTH;
    //For general reset clear, greater of TLB depth or inuse memory block (32-bits)
    localparam int CLEAR_DEPTH = ENABLE_S_MODE ? TLB_CLEAR_DEPTH : 32;

    ////////////////////////////////////////////////////
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

    typedef enum {RST_STATE, IDLE_STATE, TLB_CLEAR_STATE, IQ_DRAIN, IQ_DISCARD} gc_state;
    gc_state state;
    gc_state next_state;

    logic tlb_clear_done;

    logic i_fence_flush;
    exception_code_t ecall_code;
    logic second_cycle_flush;

    //CSR
    logic mret;
    logic sret;
    logic [XLEN-1:0] wb_csr;
    csr_inputs_t csr_inputs;
    exception_packet_t gc_exception;
    exception_packet_t csr_exception;
    logic [1:0] current_privilege;
    logic [31:0] trap_pc;
    logic [31:0] csr_mepc;
    logic [31:0] csr_sepc;

    //Write-back handshaking
    logic [2:0] fn3;
    logic [6:0] opcode;
    logic [4:0] opcode_trim;

    logic [4:0] rs1_addr;
    logic [4:0] rs2_addr;
    logic [4:0] future_rd_addr;

    logic is_csr;
    logic processing_csr;
    logic csr_ready_to_complete;
    logic csr_ready_to_complete_r;
    instruction_id_t instruction_id;
    //implementation
    ////////////////////////////////////////////////////


    //Instruction decode
    assign opcode = gc_inputs.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn3 = gc_inputs.instruction[14:12];
    assign rs1_addr = gc_inputs.instruction[19:15];

    ////////////////////////////////////////////////////
    //GC Operation
    assign is_csr = issue.new_request_r & gc_inputs.is_csr;

    assign gc_fetch_flush = branch_flush | gc_fetch_pc_override;

    always_ff @ (posedge clk) begin
        gc_issue_hold <= issue.new_request || is_csr || processing_csr || (next_state inside {TLB_CLEAR_STATE, IQ_DRAIN, IQ_DISCARD});
    end

    always_ff @ (posedge clk) begin
        gc_issue_flush <= (next_state == IQ_DISCARD);
    end

    always_ff @ (posedge clk) begin
        gc_supress_writeback <= next_state inside {TLB_CLEAR_STATE, IQ_DISCARD} ? 1 : 0;
    end

    ////////////////////////////////////////////////////
    //GC State Machine
    always @(posedge clk) begin
        if (rst)
            state <= RST_STATE;
        else
            state <= next_state;
    end

    always_comb begin
        next_state = state;
        case (state)
            RST_STATE : next_state = IDLE_STATE;
            IDLE_STATE : if (ls_exception_valid) next_state = IQ_DISCARD;
            TLB_CLEAR_STATE : if (tlb_clear_done) next_state = IDLE_STATE;
            IQ_DRAIN : if (ls_exception.id == oldest_id) next_state = IQ_DISCARD;
            IQ_DISCARD : if (instruction_queue_empty) next_state = IDLE_STATE;
            default : next_state = RST_STATE;
        endcase
    end

    //Counters for tlb clearing states
    shift_counter #(.DEPTH(TLB_CLEAR_DEPTH)) tlb_clear_counter (.*, .start((state == IDLE_STATE) && (next_state == TLB_CLEAR_STATE)), .done(tlb_clear_done));

    ////////////////////////////////////////////////////
    //Exception handling
    logic ls_exception_first_cycle;
    logic ls_exception_second_cycle;

    assign ls_exception_first_cycle =  ls_exception_valid;
    always_ff @ (posedge clk) begin
        ls_exception_second_cycle <= ls_exception_first_cycle;
    end

    always_comb begin
        case (current_privilege)
            USER_PRIVILEGE : ecall_code = ECALL_U;
            SUPERVISOR_PRIVILEGE : ecall_code = ECALL_S;
            MACHINE_PRIVILEGE : ecall_code = ECALL_M;
            default : ecall_code = ECALL_U;
        endcase
    end

    assign gc_exception.code =
        ls_exception_second_cycle ? ls_exception.code :
        gc_inputs.is_ecall ? ecall_code : BREAK;
    assign gc_exception.pc = ls_exception_second_cycle ? ls_exception.pc : gc_inputs.pc;
    assign gc_exception.tval = ls_exception_second_cycle ? ls_exception.tval : '0;
    assign gc_exception.valid = gc_inputs.is_ecall | gc_inputs.is_ebreak | ls_exception_second_cycle;

    always_ff @ (posedge clk) begin
        second_cycle_flush <= gc_flush_required;
        gc_fetch_pc_override <= gc_flush_required | second_cycle_flush | ls_exception_first_cycle;
        gc_fetch_pc <=
            gc_inputs.is_i_fence ? gc_inputs.pc + 4 :
            gc_inputs.is_ret ? csr_mepc :
            trap_pc;
    end

    ////////////////////////////////////////////////////
    //CSR registers
    assign csr_inputs.rs1 = fn3[2] ? {27'b0, rs1_addr} : gc_inputs.rs1;
    assign csr_inputs.csr_addr = gc_inputs.instruction[31:20];
    assign csr_inputs.csr_op = fn3[1:0];
    assign csr_inputs.rs1_is_zero = (rs1_addr == 0);
    assign csr_inputs.rd_is_zero = gc_inputs.rd_is_zero;

    csr_regs csr_registers (.*, .new_request(is_csr), .read_regs(csr_ready_to_complete), .commit(csr_ready_to_complete_r));

    ////////////////////////////////////////////////////
    //Decode / Write-back Handshaking
    //CSR reads are passed through the Load-Store unit
    //A CSR write is only committed once it is the oldest instruction in the pipeline
    //while processing a csr operation, gc_issue_hold prevents further instructions from being issued
    assign issue.ready = 1;

    always_ff @(posedge clk) begin
        if (rst)
            processing_csr <= 0;
        else if (csr_ready_to_complete)
            processing_csr <= 0;
        else if (is_csr)
            processing_csr <= 1;
    end

    assign csr_ready_to_complete = (is_csr | processing_csr) && (oldest_id == csr_id);
    always_ff @(posedge clk) begin
        csr_ready_to_complete_r <= csr_ready_to_complete;
        csr_id <= instruction_id;
        if (issue.new_request) begin
            instruction_id <= issue.instruction_id;
        end
    end

    assign csr_done = csr_ready_to_complete_r;
    assign csr_rd = wb_csr;

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////

endmodule
