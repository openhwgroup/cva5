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
        logic dirty;
        logic globe;
        logic user;
        logic execute;
        logic write;
        logic read;
    } tlb_entry_t;

    typedef struct packed {
        logic valid;
        logic [ASIDLEN-1:0] asid;
        logic [TAG_W_S-1:0] tag;
        //Signals from the PTE
        logic [9:0] ppn1;
        logic dirty;
        logic globe;
        logic user;
        logic execute;
        logic write;
        logic read;
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
    logic [$clog2(DEPTH)-1:0] tlb_raddr;
    logic [$clog2(DEPTH)-1:0] tlb_raddr_s;
    logic [$clog2(DEPTH)-1:0] tlb_waddr;
    logic [$clog2(DEPTH)-1:0] tlb_waddr_s;
    tlb_entry_t [WAYS-1:0] rdata;
    tlb_entry_s_t rdata_s;
    logic [WAYS-1:0] write;
    logic write_s;
    tlb_entry_t wdata;
    tlb_entry_s_t wdata_s;

    generate for (genvar i = 0; i < WAYS; i++) begin : gen_lut_rams
        lutram_1w_1r #(.DATA_TYPE(tlb_entry_t), .DEPTH(DEPTH)) data_table (
            .waddr(tlb_waddr),
            .raddr(tlb_raddr),
            .ram_write(write[i]),
            .new_ram_data(wdata),
            .ram_data_out(rdata[i]),
        .*);
    end endgenerate
    lutram_1w_1r #(.DATA_TYPE(tlb_entry_s_t), .DEPTH(DEPTH)) data_table_s (
        .waddr(tlb_waddr_s),
        .raddr(tlb_raddr_s),
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
    logic [WAYS-1:0] rdata_global;
    logic rdata_global_s;
    logic [WAYS-1:0][9:0] ppn0;
    logic [WAYS-1:0][9:0] ppn1;
    logic [9:0] ppn1_s;
    logic [WAYS-1:0] perms_valid_comb;
    logic perms_valid_comb_s;
    logic [WAYS-1:0] perms_valid;
    logic perms_valid_s;
    logic [WAYS-1:0] hit_ohot;
    logic hit_ohot_s;
    logic [WAY_W-1:0] hit_way;
    logic hit;

    assign cmp_tag = sfence.valid ? sfence.addr[31-:TAG_W] : tlb.virtual_address[31-:TAG_W];
    assign cmp_tag_s = sfence.valid ? sfence.addr[31-:TAG_W_S] : tlb.virtual_address[31-:TAG_W_S];
    assign cmp_asid = sfence.valid ? sfence.asid : asid;

    always_ff @(posedge clk) begin
        for (int i = 0; i < WAYS; i++) begin
            tag_hit[i] <= rdata[i].tag == cmp_tag;
            rdata_global[i] <= rdata[i].globe;
            ppn0[i] <= rdata[i].ppn0;
            ppn1[i] <= rdata[i].ppn1;
            asid_hit[i] <= rdata[i].asid == cmp_asid;
            perms_valid[i] <= perms_valid_comb[i];
            hit_ohot[i] <= rdata[i].valid & (rdata[i].tag == cmp_tag) & (rdata[i].asid == cmp_asid | rdata[i].globe);
        end
        tag_hit_s <= rdata_s.tag == cmp_tag_s;
        rdata_global_s <= rdata_s.globe;
        ppn1_s <= rdata_s.ppn1;
        asid_hit_s <= rdata_s.asid == cmp_asid;
        perms_valid_s <= perms_valid_comb_s;
        hit_ohot_s <= rdata_s.valid & (rdata_s.tag == cmp_tag_s) & (rdata_s.asid == cmp_asid | rdata_s.globe);
    end

    assign hit = |hit_ohot | hit_ohot_s;

    priority_encoder #(.WIDTH(WAYS)) hit_cast (
        .priority_vector(hit_ohot),
        .encoded_result(hit_way)
    );

    generate for (genvar i = 0; i < WAYS; i++) begin : gen_perms_check
        perms_check checks (
            .pte_perms('{
                d : rdata[i].dirty,
                a : 1'b1,
                u : rdata[i].user,
                x : rdata[i].execute,
                w : rdata[i].write,
                r : rdata[i].read,
                default: 'x
            }),
            .rnw(tlb.rnw),
            .execute(1'b0),
            .mxr(mmu.mxr),
            .sum(mmu.sum),
            .privilege(mmu.privilege),
            .valid(perms_valid_comb[i])
        );
    end endgenerate
    perms_check checks (
        .pte_perms('{
            d : rdata_s.dirty,
            a : 1'b1,
            u : rdata_s.user,
            x : rdata_s.execute,
            w : rdata_s.write,
            r : rdata_s.read,
            default: 'x
        }),
        .rnw(tlb.rnw),
        .execute(1'b0),
        .mxr(mmu.mxr),
        .sum(mmu.sum),
        .privilege(mmu.privilege),
        .valid(perms_valid_comb_s)
    );


    //SFENCE
    logic sfence_valid_r;
    logic [$clog2(DEPTH)-1:0] flush_addr;
    lfsr #(.WIDTH($clog2(DEPTH)), .NEEDS_RESET(0)) lfsr_counter (
        .en(1'b1),
        .value(flush_addr),
    .*);

    always_ff @(posedge clk) begin
        if (tlb.new_request | sfence.valid) begin
            tlb_waddr <= tlb_raddr;
            tlb_waddr_s <= tlb_raddr_s;
        end
        sfence_valid_r <= sfence.valid; //Other SFENCE signals remain registered and do not need to be saved
    end

    always_comb begin
        if (sfence.valid) begin
            tlb_raddr = sfence.addr_only ? sfence.addr[12 +: $clog2(DEPTH)] : flush_addr;
            tlb_raddr_s = sfence.addr_only ? sfence.addr[22 +: $clog2(DEPTH)] : flush_addr;
        end
        else begin
            tlb_raddr = tlb.virtual_address[12 +: $clog2(DEPTH)];
            tlb_raddr_s = tlb.virtual_address[22 +: $clog2(DEPTH)];
        end
    end

    assign wdata = '{
        valid : ~sfence_valid_r,
        asid : asid,
        tag : mmu.virtual_address[31-:TAG_W],
        ppn1 : mmu.upper_physical_address[19:10],
        ppn0 : mmu.upper_physical_address[9:0],
        dirty : mmu.perms.d,
        globe : mmu.perms.g,
        user : mmu.perms.u,
        execute : mmu.perms.x,
        write : mmu.perms.w,
        read : mmu.perms.r
    };
    assign wdata_s = '{
        valid : ~sfence_valid_r,
        asid : asid,
        tag : mmu.virtual_address[31-:TAG_W_S],
        ppn1 : mmu.upper_physical_address[19:10],
        dirty : mmu.perms.d,
        globe : mmu.perms.g,
        user : mmu.perms.u,
        execute : mmu.perms.x,
        write : mmu.perms.w,
        read : mmu.perms.r
    };

    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            case ({sfence_valid_r, sfence.addr_only, sfence.asid_only})
                3'b100: begin //Clear everything
                    write[i] = 1'b1;
                    write_s = 1'b1;
                end
                3'b101: begin //Clear non global for specified address space
                    write[i] = ~rdata_global[i] & asid_hit[i];
                    write_s = ~rdata_global_s & asid_hit_s;
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
    logic new_request_r;
    assign mmu.request = translation_on & new_request_r & ~hit & ~perm_fail;
    assign mmu.execute = 0;

    always_ff @(posedge clk) begin
        new_request_r <= tlb.new_request;
        if (tlb.new_request) begin
            mmu.virtual_address <= tlb.virtual_address;
            mmu.rnw <= tlb.rnw;
        end
    end

    //TLB interface
    assign tlb.done = (new_request_r & ((hit & ~perm_fail) | ~translation_on)) | mmu.write_entry;
    assign tlb.ready = 1; //Not always ready, but requests will not be sent if it isn't done
    assign tlb.is_fault = mmu.is_fault | (new_request_r & translation_on & perm_fail);


    always_comb begin
        tlb.physical_address[11:0] = mmu.virtual_address[11:0];
        if (~translation_on)
            tlb.physical_address[31:12] = mmu.virtual_address[31:12];
        else if (new_request_r) begin
            tlb.physical_address[31:22] = hit_ohot_s ? ppn1_s : ppn1[hit_way];
            tlb.physical_address[21:12] = hit_ohot_s ? mmu.virtual_address[21:12] : ppn0[hit_way];
        end else begin
            tlb.physical_address[31:22] = mmu.upper_physical_address[19:10];
            tlb.physical_address[21:12] = mmu.superpage ? mmu.virtual_address[21:12] : mmu.upper_physical_address[9:0];
        end
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    request_on_miss:
        assert property (@(posedge clk) disable iff (rst) (mmu.request) |-> ~tlb.new_request)
        else $error("Request during miss in TLB!");

endmodule
