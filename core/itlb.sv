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

module itlb

    import riscv_types::*;
    import cva5_types::*;

    #(
        parameter WAYS = 2,
        parameter DEPTH = 32
    )
    (
        input logic clk,
        input logic rst,
        input logic translation_on,
        input tlb_packet_t sfence,
        input logic abort_request,
        input logic [ASIDLEN-1:0] asid,
        mmu_interface.tlb mmu,
        tlb_interface.tlb tlb
    );
    //////////////////////////////////////////
    localparam TLB_TAG_W = 32-12-$clog2(DEPTH);

    typedef struct packed {
        logic valid;
        logic is_global;
        logic [ASIDLEN-1:0] asid;
        logic [TLB_TAG_W-1:0] tag;
        logic [19:0] phys_addr;
    } tlb_entry_t;
    logic[TLB_TAG_W-1:0] virtual_tag;
    logic[WAYS-1:0] replacement_way;

    ////////////////////////////////////////////////////
    //Implementation
    //LUTRAM-based
    //SFENCE and reset are performed sequentially, coordinated by the gc unit
    logic [$clog2(DEPTH)-1:0] tlb_addr;
    tlb_entry_t rdata[WAYS];
    logic [WAYS-1:0] write;
    tlb_entry_t wdata;

    generate for (genvar i = 0; i < WAYS; i++) begin : lut_rams
        lutram_1w_1r #(.DATA_TYPE(tlb_entry_t), .DEPTH(DEPTH)) way (
            .waddr(tlb_addr),
            .raddr(tlb_addr),
            .ram_write(write[i]),
            .new_ram_data(wdata),
            .ram_data_out(rdata[i]),
        .*);
    end endgenerate

    //Hit detection
    assign virtual_tag = tlb.virtual_address[31:32-TLB_TAG_W];
    logic [WAYS-1:0] tag_hit;
    logic hit;
    always_comb begin
        for (int i = 0; i < WAYS; i++)
            tag_hit[i] = {rdata[i].valid, rdata[i].tag} == {1'b1, virtual_tag};
    end
    assign hit = |tag_hit;

    //SFENCE
    logic [$clog2(DEPTH)-1:0] flush_addr;
    lfsr #(.WIDTH($clog2(DEPTH)), .NEEDS_RESET(0)) lfsr_counter (
        .en(1'b1),
        .value(flush_addr),
    .*);

    always_comb begin
        if (sfence.valid)
            tlb_addr = sfence.addr_only ? sfence.addr[12 +: $clog2(DEPTH)] : flush_addr;
        else
            tlb_addr = tlb.virtual_address[12 +: $clog2(DEPTH)];
    end

    assign wdata = '{
        valid : ~sfence.valid,
        is_global : mmu.is_global,
        asid : asid,
        tag : virtual_tag,
        phys_addr : mmu.upper_physical_address
    };

    logic[WAYS-1:0] sfence_asid_match;
    logic[WAYS-1:0] sfence_addr_match;
    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            sfence_asid_match[i] = ~rdata[i].is_global & rdata[i].asid == sfence.asid;
            sfence_addr_match[i] = rdata[i].tag == sfence.addr[31:32-TLB_TAG_W];

            case ({sfence.valid, sfence.addr_only, sfence.asid_only})
                3'b100: write[i] = 1'b1; //Clear everything
                3'b101: write[i] = sfence_asid_match[i]; //Clear non global for specified address space
                3'b110: write[i] = sfence_addr_match[i]; //Clear matching addresses
                3'b111: write[i] = sfence_asid_match[i] & sfence_addr_match[i]; //Clear if both
                default: write[i] = mmu.write_entry & replacement_way[i];
            endcase
        end
    end

    //Random replacement
    cycler #(.C_WIDTH(WAYS)) replacement_policy (       
        .en(1'b1), 
        .one_hot(replacement_way),
    .*);

    //MMU interface
    logic request_in_progress;
    always_ff @ (posedge clk) begin
        if (rst)
            request_in_progress <= 0;
        else if (mmu.write_entry | mmu.is_fault | abort_request)
            request_in_progress <= 0;
        else if (tlb.new_request & ~hit)
            request_in_progress <= 1;
    end

    assign mmu.request = request_in_progress;
    assign mmu.execute = 1;
    assign mmu.rnw = tlb.rnw;
    assign mmu.virtual_address = tlb.virtual_address;

    //TLB interface
    logic mmu_request_complete;
    always_ff @(posedge clk) begin
        if (rst)
            mmu_request_complete <= 0;
        else
            mmu_request_complete <= mmu.write_entry;
    end
    assign tlb.done = hit & (tlb.new_request | mmu_request_complete);
    assign tlb.ready = ~request_in_progress;
    assign tlb.is_fault = mmu.is_fault;

    always_comb begin
        tlb.physical_address[11:0] = tlb.virtual_address[11:0];
        tlb.physical_address[31:12] = 0;
        for (int i = 0; i < WAYS; i++)
            if (tag_hit[i]) tlb.physical_address[31:12] |= rdata[i].phys_addr;
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