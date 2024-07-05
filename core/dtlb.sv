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

module dtlb

    import cva5_types::*;
    import riscv_types::*;

    #(
        parameter WAYS = 2,
        parameter DEPTH = 32
    )
    (
        input logic clk,
        input logic rst,
        input logic translation_on,
        input tlb_packet_t sfence,
        input logic [ASIDLEN-1:0] asid,
        mmu_interface.tlb mmu,
        tlb_interface.tlb tlb
    );
    //////////////////////////////////////////
    localparam TLB_TAG_W = 32-12-$clog2(DEPTH);

    typedef logic[TLB_TAG_W-1:0] tag_t;
    typedef logic[$clog2(DEPTH)-1:0] line_t;

    typedef struct packed {
        logic valid;
        logic is_global;
        logic [ASIDLEN-1:0] asid;
        tag_t tag;
        logic [19:0] phys_addr;
    } tlb_entry_t;

    ////////////////////////////////////////////////////
    //Implementation
    //LUTRAM-based, but with registered outputs
    //SFENCE and reset are performed sequentially, coordinated by the gc unit
    line_t raddr;
    line_t waddr;
    tlb_entry_t rdata[WAYS];
    tlb_entry_t rdata_r[WAYS];
    logic [WAYS-1:0] write;
    tlb_entry_t wdata;

    generate for (genvar i = 0; i < WAYS; i++) begin : lut_rams
        lutram_1w_1r #(.DATA_TYPE(tlb_entry_t), .DEPTH(DEPTH)) way (
            .waddr(waddr),
            .raddr(raddr),
            .ram_write(write[i]),
            .new_ram_data(wdata),
            .ram_data_out(rdata[i]),
        .*);
        always_ff @(posedge clk) rdata_r[i] <= rdata[i];
    end endgenerate

    //Hit detection
    tag_t cmp_tag;
    logic [ASIDLEN-1:0] cmp_asid;
    logic [WAYS-1:0] tag_hit;
    logic [WAYS-1:0] asid_hit;
    logic [WAYS-1:0] both_hit;
    logic hit;
    logic [19:0] tlb_addr;

    assign cmp_tag = sfence_valid_r ? sfence.addr[31:32-TLB_TAG_W] : mmu.virtual_address[31:32-TLB_TAG_W];
    assign cmp_asid = sfence_valid_r ? sfence.asid : asid;

    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            tag_hit[i] = rdata_r[i].tag == cmp_tag;
            asid_hit[i] = {rdata_r[i].valid, rdata_r[i].asid} == {1'b1, cmp_asid}; //Put valid comparison in ASID because it is narrower than the tag
        end
    end
    assign both_hit = tag_hit & asid_hit;
    assign hit = |both_hit;

    always_comb begin
        tlb_addr = '0;
        for (int i = 0; i < WAYS; i++)
            if (both_hit[i]) tlb_addr |= rdata_r[i].phys_addr;
    end

    //Random replacement
    logic[WAYS-1:0] replacement_way;
    cycler #(.C_WIDTH(WAYS)) replacement_policy (       
        .en(1'b1), 
        .one_hot(replacement_way),
    .*);

    //SFENCE
    logic sfence_valid_r;
    line_t flush_addr;
    line_t flush_addr_r;

    lfsr #(.WIDTH($clog2(DEPTH)), .NEEDS_RESET(0)) lfsr_counter (
        .en(1'b1),
        .value(flush_addr),
    .*);

    always_ff @(posedge clk) begin
        flush_addr_r <= flush_addr;
        sfence_valid_r <= sfence.valid; //Other SFENCE signals remain registered and do not need to be saved
    end

    assign waddr = sfence_valid_r ? flush_addr_r : mmu.virtual_address[12 +: $clog2(DEPTH)];
    assign raddr = sfence.valid ? flush_addr : tlb.virtual_address[12 +: $clog2(DEPTH)];

    assign wdata = '{
        valid : ~sfence_valid_r,
        is_global : mmu.is_global,
        asid : asid,
        tag : mmu.virtual_address[31:32-TLB_TAG_W],
        phys_addr : mmu.upper_physical_address
    };

    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            case ({sfence_valid_r, sfence.addr_only, sfence.asid_only})
                3'b100: write[i] = 1'b1; //Clear everything
                3'b101: write[i] = asid_hit[i]; //Clear non global for specified address space
                3'b110: write[i] = tag_hit[i]; //Clear matching addresses
                3'b111: write[i] = both_hit[i]; //Clear if both
                default: write[i] = mmu.write_entry & replacement_way[i];
            endcase
        end
    end

    //MMU interface
    logic new_request_r;
    always_ff @(posedge clk) new_request_r <= tlb.new_request;

    assign mmu.request = new_request_r & ~hit & translation_on;
    assign mmu.execute = 0;
    always_ff @(posedge clk) begin
        if (tlb.new_request) begin
            mmu.virtual_address <= tlb.virtual_address;
            mmu.rnw <= tlb.rnw;
        end
    end

    //TLB interface
    assign tlb.done = (new_request_r & (hit | ~translation_on)) | (mmu.write_entry);
    assign tlb.ready = 1; //Not always ready, but requests will not be sent if it isn't done
    assign tlb.is_fault = mmu.is_fault;

    always_comb begin
        tlb.physical_address[11:0] = mmu.virtual_address[11:0];
        if (~translation_on)
            tlb.physical_address[31:12] = mmu.virtual_address[31:12];
        else if (new_request_r)
            tlb.physical_address[31:12] = tlb_addr;
        else
            tlb.physical_address[31:12] = mmu.upper_physical_address;
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    multiple_tag_hit_in_tlb:
        assert property (@(posedge clk) disable iff (rst) (tlb.new_request & translation_on) |=> $onehot(both_hit))
        else $error("Multiple tag hits in TLB!");

    request_on_miss:
        assert property (@(posedge clk) disable iff (rst) (new_request_r & translation_on & ~hit) |-> ~tlb.new_request)
        else $error("Request during miss in TLB!");

endmodule