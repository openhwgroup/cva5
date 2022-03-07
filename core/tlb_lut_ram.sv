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



module tlb_lut_ram

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    #(
        parameter WAYS = 2,
        parameter DEPTH = 32
    )
    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,
        input logic abort_request,
        input logic [ASIDLEN-1:0] asid,
        mmu_interface.tlb mmu,
        tlb_interface.tlb tlb
    );
    //////////////////////////////////////////
    localparam TLB_TAG_W = 32-12-$clog2(DEPTH);

    typedef struct packed {
        logic valid;
        logic [TLB_TAG_W-1:0] tag;
        logic [19:0] phys_addr;
    } tlb_entry_t;

    logic [$clog2(DEPTH)-1:0] tlb_addr;
    logic [TLB_TAG_W-1:0] virtual_tag;

    tlb_entry_t ram [DEPTH-1:0][WAYS-1:0];
    logic [DEPTH-1:0] valid [WAYS-1:0];

    logic [WAYS-1:0] tag_hit;
    logic hit;
    logic [WAYS-1:0] replacement_way;

    logic [$bits(tlb_entry_t)-1:0] ram_data [WAYS-1:0];
    tlb_entry_t ram_entry [WAYS-1:0];
    tlb_entry_t new_entry;

    logic [$clog2(DEPTH)-1:0] flush_addr;

    logic [WAYS-1:0] tlb_write;
    logic request_in_progress;
    logic mmu_request_complete;
    ////////////////////////////////////////////////////
    //Implementation
    //LUTRAM-based
    //Reset is performed sequentially, coordinated by the gc unit

    lfsr #(.WIDTH($clog2(DEPTH)), .NEEDS_RESET(0))
    lfsr_counter (
        .clk (clk), .rst (rst),
        .en(gc.tlb_flush),
        .value(flush_addr)
    );

    assign tlb_addr = gc.tlb_flush ? flush_addr : tlb.virtual_address[12 +: $clog2(DEPTH)];
    assign tlb_write = {WAYS{gc.tlb_flush}}  | replacement_way;

    assign new_entry.valid = ~gc.tlb_flush;
    assign new_entry.tag = virtual_tag;
    assign new_entry.phys_addr = mmu.upper_physical_address;

    genvar i;
    generate
        for (i=0; i<WAYS; i=i+1) begin : lut_rams
            lutram_1w_1r #(.WIDTH($bits(tlb_entry_t)), .DEPTH(DEPTH))
            write_port (
                .clk(clk),
                .waddr(tlb_addr),
                .raddr(tlb_addr),
                .ram_write(tlb_write[i]),
                .new_ram_data(new_entry),
                .ram_data_out(ram_data[i])
            );
            assign ram_entry[i] = ram_data[i];
        end
    endgenerate

    cycler #(.C_WIDTH(WAYS)) replacement_policy (       
        .clk        (clk),
        .rst        (rst), 
        .en         (1'b1), 
        .one_hot    (replacement_way)
    );

    assign virtual_tag = tlb.virtual_address[31:32-TLB_TAG_W];

    always_comb begin
        for (int i=0; i<WAYS; i=i+1) begin
            tag_hit[i] = {ram_entry[i].valid, ram_entry[i].tag} == {1'b1, virtual_tag};
        end
    end

    assign tlb.ready = ~request_in_progress;

    always_ff @ (posedge clk) begin
        if (rst)
            request_in_progress <= 0;
        else if (mmu.write_entry | mmu.is_fault | abort_request)
            request_in_progress <= 0;
        else if (tlb.new_request & ~hit)
            request_in_progress <= 1;
    end
    
    assign mmu.request = request_in_progress;

    always_ff @ (posedge clk) begin
        if (rst)
            mmu_request_complete <= 0;
        else
            mmu_request_complete <= mmu.write_entry;
    end

    assign mmu.virtual_address = tlb.virtual_address;
    assign mmu.execute = tlb.execute;
    assign mmu.rnw = tlb.rnw;

    //On a TLB miss, the entry is requested from the MMU
    //Once the request completes, it will update the TLB, causing
    //the current request to output a hit
    assign hit = |tag_hit;
    assign tlb.done = hit & (tlb.new_request | mmu_request_complete);
    assign tlb.is_fault = mmu.is_fault;

    always_comb begin
        tlb.physical_address[11:0] = tlb.virtual_address[11:0];
        tlb.physical_address[31:12] = 0;
        for (int i = 0; i < WAYS; i++) begin
            if (tag_hit[i])  tlb.physical_address[31:12] |= ram_entry[i].phys_addr;
        end
    end
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    multiple_tag_hit_in_tlb:
        assert property (@(posedge clk) disable iff (rst) (tlb.done) |-> $onehot(tag_hit))
        else $error("Multiple tag hits in TLB!");

endmodule