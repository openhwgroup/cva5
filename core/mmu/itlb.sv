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
    localparam TAG_W = 20 - $clog2(DEPTH);
    localparam TAG_W_S = 10 - $clog2(DEPTH);
    localparam WAY_W = WAYS == 1 ? 1 : $clog2(WAYS);

    typedef struct packed {
        logic valid;
        logic [ASIDLEN-1:0] asid;
        logic [TAG_W-1:0] tag;
        //Signals from the PTE
        logic [9:0] ppn1;
        logic [9:0] ppn0;
        logic globe;
        logic user;
    } tlb_entry_t;

    typedef struct packed {
        logic valid;
        logic [ASIDLEN-1:0] asid;
        logic [TAG_W_S-1:0] tag;
        //Signals from the PTE
        logic [9:0] ppn1;
        logic globe;
        logic user;
    } tlb_entry_s_t;

    ////////////////////////////////////////////////////
    //Implementation
    //Regular and super pages stored separately
    //Regular pages are set associative and super pages are direct mapped

    //Random replacement
    logic[WAYS-1:0] replacement_way;
    cycler #(.C_WIDTH(WAYS)) replacement_policy (       
        .en(1'b1), 
        .one_hot(replacement_way),
    .*);
    
    //LUTRAM storage
    logic [$clog2(DEPTH)-1:0] tlb_addr;
    logic [$clog2(DEPTH)-1:0] tlb_addr_s;
    tlb_entry_t [WAYS-1:0] rdata;
    tlb_entry_s_t rdata_s;
    logic [WAYS-1:0] write;
    logic write_s;
    tlb_entry_t wdata;
    tlb_entry_s_t wdata_s;

    generate for (genvar i = 0; i < WAYS; i++) begin : gen_lut_rams
        lutram_1w_1r #(.DATA_TYPE(tlb_entry_t), .DEPTH(DEPTH)) data_table (
            .waddr(tlb_addr),
            .raddr(tlb_addr),
            .ram_write(write[i]),
            .new_ram_data(wdata),
            .ram_data_out(rdata[i]),
        .*);
    end endgenerate
    lutram_1w_1r #(.DATA_TYPE(tlb_entry_s_t), .DEPTH(DEPTH)) data_table_s (
        .waddr(tlb_addr_s),
        .raddr(tlb_addr_s),
        .ram_write(write_s),
        .new_ram_data(wdata_s),
        .ram_data_out(rdata_s),
    .*);


    //Hit detection
    logic [TAG_W-1:0] cmp_tag;
    logic [TAG_W_S-1:0] cmp_tag_s;
    logic [ASIDLEN-1:0] cmp_asid;
    logic [WAYS-1:0] tag_hit;
    logic tag_hit_s;
    logic [WAYS-1:0] asid_hit;
    logic asid_hit_s;
    logic [WAYS-1:0] perms_valid;
    logic perms_valid_s;
    logic [WAYS-1:0] hit_ohot;
    logic hit_ohot_s;
    logic [WAY_W-1:0] hit_way;
    logic hit;

    assign cmp_tag = sfence.valid ? sfence.addr[31-:TAG_W] : tlb.virtual_address[31-:TAG_W];
    assign cmp_tag_s = sfence.valid ? sfence.addr[31-:TAG_W_S] : tlb.virtual_address[31-:TAG_W_S];
    assign cmp_asid = sfence.valid ? sfence.asid : asid;

    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            tag_hit[i] = rdata[i].tag == cmp_tag;
            asid_hit[i] = rdata[i].asid == cmp_asid;
            hit_ohot[i] = rdata[i].valid & tag_hit[i] & (asid_hit[i] | rdata[i].globe);
        end
        tag_hit_s = rdata_s.tag == cmp_tag_s;
        asid_hit_s = rdata_s.asid == cmp_asid;
        hit_ohot_s = rdata_s.valid & tag_hit_s & (asid_hit_s | rdata_s.globe);
    end
    assign hit = |hit_ohot | hit_ohot_s;

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
    perms_check checks_s (
        .pte_perms('{
            x : 1'b1,
            a : 1'b1,
            u : rdata_s.user,
            default: 'x
        }),
        .rnw(tlb.rnw),
        .execute(1'b1),
        .mxr(mmu.mxr),
        .sum(mmu.sum),
        .privilege(mmu.privilege),
        .valid(perms_valid_s)
    );


    //SFENCE
    logic [$clog2(DEPTH)-1:0] flush_addr;
    lfsr #(.WIDTH($clog2(DEPTH)), .NEEDS_RESET(0)) lfsr_counter (
        .en(1'b1),
        .value(flush_addr),
    .*);

    always_comb begin
        if (sfence.valid) begin
            tlb_addr = sfence.addr_only ? sfence.addr[12 +: $clog2(DEPTH)] : flush_addr;
            tlb_addr_s = sfence.addr_only ? sfence.addr[22 +: $clog2(DEPTH)] : flush_addr;
        end
        else begin
            tlb_addr = tlb.virtual_address[12 +: $clog2(DEPTH)];
            tlb_addr_s = tlb.virtual_address[22 +: $clog2(DEPTH)];
        end
    end

    assign wdata = '{
        valid : ~sfence.valid,
        asid : asid,
        tag : tlb.virtual_address[31-:TAG_W],
        ppn1 : mmu.upper_physical_address[19:10],
        ppn0 : mmu.upper_physical_address[9:0],
        globe : mmu.perms.g,
        user : mmu.perms.u
    };
    assign wdata_s = '{
        valid : ~sfence.valid,
        asid : asid,
        tag : tlb.virtual_address[31-:TAG_W_S],
        ppn1 : mmu.upper_physical_address[19:10],
        globe : mmu.perms.g,
        user : mmu.perms.u
    };

    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            case ({sfence.valid, sfence.addr_only, sfence.asid_only})
                3'b100: begin //Clear everything
                    write[i] = 1'b1;
                    write_s = 1'b1;
                end
                3'b101: begin //Clear non global for specified address space
                    write[i] = ~rdata[i].globe & asid_hit[i];
                    write_s = ~rdata_s.globe & asid_hit_s;
                end
                3'b110: begin //Clear matching addresses
                    write[i] = tag_hit[i];
                    write_s = tag_hit_s;
                end
                3'b111: begin //Clear if both  
                    write[i] = (~rdata[i].globe & asid_hit[i]) & tag_hit[i];
                    write_s = (~rdata_s.globe & asid_hit_s) & tag_hit_s;
                end
                default: begin
                    write[i] = mmu.write_entry & ~mmu.superpage & replacement_way[i];
                    write_s = mmu.write_entry & mmu.superpage;
                end
            endcase
        end
    end

    //Permission fail
    logic perm_fail;
    assign perm_fail = |(hit_ohot & ~perms_valid) | (hit_ohot_s & ~perms_valid_s);

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
    assign tlb.ready = ~request_in_progress & ~mmu_request_complete;
    assign tlb.is_fault = mmu.is_fault | (tlb.new_request & translation_on & perm_fail);

    always_comb begin
        tlb.physical_address[11:0] = tlb.virtual_address[11:0];
        if (~translation_on)
            tlb.physical_address[31:12] = tlb.virtual_address[31:12];
        else if (hit_ohot_s) begin
            tlb.physical_address[21:12] = tlb.virtual_address[21:12];
            tlb.physical_address[31:22] = rdata_s.ppn1;
        end
        else begin
            tlb.physical_address[21:12] = rdata[hit_way].ppn0;
            tlb.physical_address[31:22] = rdata[hit_way].ppn1;
        end
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
