/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

module mmu

    import csr_types::*;

    (
        input logic clk,
        input logic rst,
        mmu_interface.mmu mmu,
        input logic abort_request,
        mem_interface.ro_master mem
    );

    typedef struct packed{
        logic [11:0] ppn1;
        logic [9:0] ppn0;
        logic [1:0] reserved;
        pte_perms_t perms;
    } pte_t;

    typedef enum  {
        IDLE = 0,
        SEND_REQUEST_1 = 1,
        WAIT_REQUEST_1 = 2,
        SEND_REQUEST_2 = 3,
        WAIT_REQUEST_2 = 4,
        COMPLETE_SUCCESS = 5,
        COMPLETE_FAULT = 6
    } mmu_state_t;
    logic [6:0] state;
    logic [6:0] next_state;

    pte_t pte;
    logic perms_valid;

    localparam MAX_ABORTED_REQUESTS = 4;
    logic abort_queue_full;
    logic discard_data;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //L1 arbiter Interfrace
    assign mem.rlen = '0;

    assign mem.request = (state[SEND_REQUEST_1] | state[SEND_REQUEST_2]) & ~abort_request;

    //Page Table addresses
    always_ff @ (posedge clk) begin
        if (state[IDLE] | (mem.rvalid & ~discard_data)) begin
            if (state[IDLE])
                mem.addr <= {mmu.satp_ppn[19:0], mmu.virtual_address[31:22]};
            else
                mem.addr <= {pte.ppn1[9:0], pte.ppn0, mmu.virtual_address[21:12]};
        end
    end

    assign pte = mem.rdata;

    ////////////////////////////////////////////////////
    //Supports unlimited tracking of aborted requests
    //Assumption: memory requests are returned in-order
    localparam COUNT_W = $clog2(MAX_ABORTED_REQUESTS);
    logic [COUNT_W:0] abort_tracking;
    logic delayed_abort;
    logic delayed_abort_complete;

    assign delayed_abort = abort_request & (state[WAIT_REQUEST_1] | state[WAIT_REQUEST_2]);
    assign delayed_abort_complete = (discard_data | abort_request) & mem.rvalid;
    always_ff @ (posedge clk) begin
        if (rst)
            abort_tracking <= 0;
        else
            abort_tracking <= abort_tracking - COUNT_W'(delayed_abort) + COUNT_W'(delayed_abort_complete);
    end

    assign discard_data = abort_tracking[COUNT_W];
    assign abort_queue_full = abort_tracking[COUNT_W] & ~|abort_tracking[COUNT_W-1:0];

    perms_check perm (
        .pte_perms(pte.perms),
        .rnw(mmu.rnw),
        .execute(mmu.execute),
        .mxr(mmu.mxr),
        .sum(mmu.sum),
        .privilege(mmu.privilege),
        .valid(perms_valid)
    );

    ////////////////////////////////////////////////////
    //State Machine
    always_comb begin
        next_state = state;
        case (1'b1)
            state[IDLE] :
                if (mmu.request & ~abort_queue_full)
                    next_state = 2**SEND_REQUEST_1;
            state[SEND_REQUEST_1] : 
                if (mem.ack)
                    next_state = 2**WAIT_REQUEST_1;
            state[WAIT_REQUEST_1] :
                if (mem.rvalid & ~discard_data) begin
                    if (~pte.perms.v | (~pte.perms.r & pte.perms.w)) //page not valid OR invalid xwr pattern
                        next_state = 2**COMPLETE_FAULT;
                    else if (pte.perms.v & (pte.perms.r | pte.perms.x)) begin//superpage (all remaining xwr patterns other than all zeros)
                        if (perms_valid & ~|pte.ppn0) //check for misaligned superpage
                            next_state = 2**COMPLETE_SUCCESS;
                        else
                            next_state = 2**COMPLETE_FAULT;
                    end else //(pte.perms.v & ~pte.perms.x & ~pte.perms.w & ~pte.perms.r) pointer to next level in page table
                        next_state = 2**SEND_REQUEST_2;
                end
            state[SEND_REQUEST_2] : 
                if (mem.ack)
                    next_state = 2**WAIT_REQUEST_2;
            state[WAIT_REQUEST_2] : 
                if (mem.rvalid & ~discard_data) begin
                    if (~perms_valid | ~pte.perms.v | (~pte.perms.r & pte.perms.w)) //perm fail or invalid
                        next_state = 2**COMPLETE_FAULT;
                    else
                        next_state = 2**COMPLETE_SUCCESS;
                end
            state[COMPLETE_SUCCESS], state[COMPLETE_FAULT]  :
                next_state = 2**IDLE;
        endcase
        //If request is aborted, return to IDLE
        if (abort_request)
            next_state = 2**IDLE;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            state <= 2**IDLE;
        else
            state <= next_state;
    end

    ////////////////////////////////////////////////////
    //TLB return path
    always_ff @ (posedge clk) begin
        if (mem.rvalid) begin
            mmu.superpage <= state[WAIT_REQUEST_1];
            mmu.perms.d <= pte.perms.d;
            mmu.perms.a <= pte.perms.a;
            mmu.perms.g <= pte.perms.g | (state[WAIT_REQUEST_2] & mmu.perms.g);
            mmu.perms.u <= pte.perms.u;
            mmu.perms.x <= pte.perms.x;
            mmu.perms.w <= pte.perms.w;
            mmu.perms.r <= pte.perms.r;
            mmu.perms.v <= pte.perms.v;
            mmu.upper_physical_address[19:10] <= pte.ppn1[9:0];
            mmu.upper_physical_address[9:0] <= state[WAIT_REQUEST_2] ? pte.ppn0 : mmu.virtual_address[21:12];
        end
    end
    assign mmu.write_entry = state[COMPLETE_SUCCESS];
    assign mmu.is_fault = state[COMPLETE_FAULT];

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    mmu_spurious_l1_response:
        assert property (@(posedge clk) disable iff (rst) (mem.rvalid) |-> (state[WAIT_REQUEST_1] | state[WAIT_REQUEST_2]))
        else $error("mmu recieved response without a request");

    //TLB request remains high until it recieves a response from the MMU unless
    //the transaction is aborted.  As such, if TLB request is low and we are not in the
    //IDLE state, then our current processor state has been corrupted
    mmu_tlb_state_mismatch:
        assert property (@(posedge clk) disable iff (rst) (mmu.request) |-> (state[IDLE]))
        else $error("MMU and TLB state mismatch");

endmodule
