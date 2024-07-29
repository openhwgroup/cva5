/*
 * Copyright © 2017 Eric Matthews, Chris Keilbart, Lesley Shannon
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
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
    localparam SUPERPAGE_W = 10-$clog2(DEPTH);
    localparam NONSUPERPAGE_W = 32-12-SUPERPAGE_W-$clog2(DEPTH);
    localparam WAY_W = WAYS == 1 ? 1 : $clog2(WAYS);

    typedef struct packed {
        logic superpage;
        logic [ASIDLEN-1:0] asid;
        logic [SUPERPAGE_W-1:0] lower_tag;
        logic [NONSUPERPAGE_W-1:0] upper_tag;
        //Signals from the PTE
        logic [9:0] ppn1;
        logic [9:0] ppn0;
        logic globe;
        logic user;
    } tlb_entry_t;

    logic[WAYS-1:0] replacement_way;

    ////////////////////////////////////////////////////
    //Implementation
    //LUTRAM-based
    //SFENCE and reset are performed sequentially, coordinated by the gc unit
    logic [$clog2(DEPTH)-1:0] tlb_addr;
    tlb_entry_t rdata[WAYS];
    logic [WAYS-1:0] rdata_valid;
    logic [WAYS-1:0] write;
    tlb_entry_t wdata;
    logic wdata_valid;

    generate for (genvar i = 0; i < WAYS; i++) begin : gen_lut_rams
        lutram_1w_1r #(.DATA_TYPE(logic), .DEPTH(DEPTH)) valid_table (
            .waddr(tlb_addr),
            .raddr(tlb_addr),
            .ram_write(write[i]),
            .new_ram_data(wdata_valid),
            .ram_data_out(rdata_valid[i]),
        .*);

        lutram_1w_1r #(.DATA_TYPE(tlb_entry_t), .DEPTH(DEPTH)) data_table (
            .waddr(tlb_addr),
            .raddr(tlb_addr),
            .ram_write(write[i]),
            .new_ram_data(wdata),
            .ram_data_out(rdata[i]),
        .*);
    end endgenerate

    //Hit detection
    logic [SUPERPAGE_W-1:0] virtual_tag_lower;
    logic [NONSUPERPAGE_W-1:0] virtual_tag_upper;
    logic [SUPERPAGE_W-1:0] cmp_tag_lower;
    logic [NONSUPERPAGE_W-1:0] cmp_tag_upper;
    logic [ASIDLEN-1:0] cmp_asid;
    logic [WAYS-1:0] lower_tag_hit;
    logic [WAYS-1:0] upper_tag_hit;
    logic [WAYS-1:0] asid_hit;
    logic [WAYS-1:0] rdata_superpage;
    logic [WAYS-1:0] perms_valid;
    logic [WAYS-1:0] hit_ohot;
    logic hit;
    logic [WAY_W-1:0] hit_way;

    assign {virtual_tag_upper, virtual_tag_lower} = tlb.virtual_address[31-:NONSUPERPAGE_W+SUPERPAGE_W];

    assign cmp_tag_upper = sfence.valid ? sfence.addr[31-:NONSUPERPAGE_W] : virtual_tag_upper;
    assign cmp_tag_lower = sfence.valid ? sfence.addr[31-NONSUPERPAGE_W-:SUPERPAGE_W] : virtual_tag_lower;
    assign cmp_asid = sfence.valid ? sfence.asid : asid;

    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            lower_tag_hit[i] = {rdata_valid[i], rdata[i].lower_tag} == {1'b1, cmp_tag_lower}; //Put valid in cmp with narrowest field for speed
            rdata_superpage[i] = rdata[i].superpage;
            upper_tag_hit[i] = rdata[i].upper_tag == cmp_tag_upper;
            asid_hit[i] = rdata[i].asid == cmp_asid;
            hit_ohot[i] = lower_tag_hit[i] & (upper_tag_hit[i] | rdata_superpage[i]) & (asid_hit[i] | rdata[i].globe);
        end
    end
    assign hit = |hit_ohot;

    priority_encoder #(.WIDTH(WAYS)) hit_cast (
        .priority_vector(hit_ohot),
        .encoded_result(hit_way)
    );

    generate for (genvar i = 0; i < WAYS; i++) begin : gen_perms_check
        perms_check checks (
            .pte_perms('{
                x : 1'b1,
                a : 1'b1,
                u : rdata[i].user,
                default: 'x
            }),
            .rnw(tlb.rnw),
            .execute(1'b1),
            .mxr(mmu.mxr),
            .sum(mmu.sum),
            .privilege(mmu.privilege),
            .valid(perms_valid[i])
        );
    end endgenerate

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

    assign wdata_valid = ~sfence.valid;
    assign wdata = '{
        superpage : mmu.superpage,
        asid : asid,
        lower_tag : virtual_tag_lower,
        upper_tag : virtual_tag_upper,
        ppn1 : mmu.upper_physical_address[19:10],
        ppn0 : mmu.upper_physical_address[9:0],
        globe : mmu.perms.g,
        user : mmu.perms.u
    };

    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            case ({sfence.valid, sfence.addr_only, sfence.asid_only})
                3'b100: write[i] = 1'b1; //Clear everything
                3'b101: write[i] = ~rdata[i].globe & asid_hit[i]; //Clear non global for specified address space
                3'b110: write[i] = lower_tag_hit[i] & (upper_tag_hit[i] | rdata_superpage[i]); //Clear matching addresses
                3'b111: write[i] = (~rdata[i].globe & asid_hit[i]) & lower_tag_hit[i] & (upper_tag_hit[i] | rdata_superpage[i]); //Clear if both
                default: write[i] = mmu.write_entry & replacement_way[i];
            endcase
        end
    end

    //Permission fail
    logic perm_fail;
    logic perm_fail_r;
    assign perm_fail = |(hit_ohot & ~perms_valid);

    always_ff @(posedge clk) begin
        if (rst)
            perm_fail_r <= 0;
        else
            perm_fail_r <= translation_on & tlb.new_request & perm_fail;
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
        else if (mmu.request)
            request_in_progress <= 1;
    end

    assign mmu.request = translation_on & tlb.new_request & ~hit & ~perm_fail;
    assign mmu.execute = 1;
    assign mmu.rnw = tlb.rnw;
    assign mmu.virtual_address = tlb.virtual_address;

    //TLB interface
    logic mmu_request_complete;
    always_ff @(posedge clk) begin
        if (rst)
            mmu_request_complete <= 0;
        else
            mmu_request_complete <= mmu.write_entry & ~abort_request;
    end
    assign tlb.done = translation_on ? (hit & ~perm_fail & (tlb.new_request | mmu_request_complete)) : tlb.new_request;
    assign tlb.ready = ~request_in_progress & ~mmu_request_complete & ~perm_fail_r;
    assign tlb.is_fault = mmu.is_fault | perm_fail_r;

    always_comb begin
        tlb.physical_address[11:0] = tlb.virtual_address[11:0];
        tlb.physical_address[31:22] = translation_on ? rdata[hit_way].ppn1 : tlb.virtual_address[31:22];
        tlb.physical_address[21:12] = ~translation_on | rdata_superpage[hit_way] ? tlb.virtual_address[21:12] : rdata[hit_way].ppn0;
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule