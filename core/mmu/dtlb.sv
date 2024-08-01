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
    localparam SUPERPAGE_W = 10-$clog2(DEPTH);
    localparam NONSUPERPAGE_W = 10;
    localparam WAY_W = WAYS == 1 ? 1 : $clog2(WAYS);

    typedef struct packed {
        logic superpage;
        logic [ASIDLEN-1:0] asid;
        logic [SUPERPAGE_W-1:0] lower_tag;
        logic [NONSUPERPAGE_W-1:0] upper_tag;
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

    logic[WAYS-1:0] replacement_way;

    ////////////////////////////////////////////////////
    //Implementation
    //LUTRAM-based
    //SFENCE and reset are performed sequentially, coordinated by the gc unit
    logic [$clog2(DEPTH)-1:0] tlb_raddr;
    logic [$clog2(DEPTH)-1:0] tlb_waddr;
    tlb_entry_t rdata[WAYS];
    logic [WAYS-1:0] rdata_valid;
    logic [WAYS-1:0] write;
    tlb_entry_t wdata;
    logic wdata_valid;

    generate for (genvar i = 0; i < WAYS; i++) begin : gen_lut_rams
        lutram_1w_1r #(.DATA_TYPE(logic), .DEPTH(DEPTH)) valid_table (
            .waddr(tlb_waddr),
            .raddr(tlb_raddr),
            .ram_write(write[i]),
            .new_ram_data(wdata_valid),
            .ram_data_out(rdata_valid[i]),
        .*);

        lutram_1w_1r #(.DATA_TYPE(tlb_entry_t), .DEPTH(DEPTH)) data_table (
            .waddr(tlb_waddr),
            .raddr(tlb_raddr),
            .ram_write(write[i]),
            .new_ram_data(wdata),
            .ram_data_out(rdata[i]),
        .*);
    end endgenerate

    //Hit detection
    logic [SUPERPAGE_W-1:0] cmp_tag_lower;
    logic [NONSUPERPAGE_W-1:0] cmp_tag_upper;
    logic [ASIDLEN-1:0] cmp_asid;
    logic [WAYS-1:0] lower_tag_hit;
    logic [WAYS-1:0] upper_tag_hit;
    logic [WAYS-1:0] asid_hit;
    logic [WAYS-1:0] rdata_superpage;
    logic [WAYS-1:0] rdata_global;
    logic [WAYS-1:0][9:0] ppn0;
    logic [WAYS-1:0][9:0] ppn1;
    logic [WAYS-1:0] perms_valid_comb;
    logic [WAYS-1:0] perms_valid;
    logic [WAYS-1:0] hit_ohot;
    logic hit;
    logic [WAY_W-1:0] hit_way;

    assign cmp_tag_upper = sfence.valid ? sfence.addr[31-:NONSUPERPAGE_W] : tlb.virtual_address[31-:NONSUPERPAGE_W];
    assign cmp_tag_lower = sfence.valid ? sfence.addr[31-NONSUPERPAGE_W-:SUPERPAGE_W] : tlb.virtual_address[31-NONSUPERPAGE_W-:SUPERPAGE_W];
    assign cmp_asid = sfence.valid ? sfence.asid : asid;

    always_ff @(posedge clk) begin
        for (int i = 0; i < WAYS; i++) begin
            lower_tag_hit[i] <= {rdata_valid[i], rdata[i].lower_tag} == {1'b1, cmp_tag_lower}; //Put valid in cmp with narrowest field for speed
            rdata_superpage[i] <= rdata[i].superpage;
            rdata_global[i] <= rdata[i].globe;
            ppn0[i] <= rdata[i].ppn0;
            ppn1[i] <= rdata[i].ppn1;
            upper_tag_hit[i] <= rdata[i].upper_tag == cmp_tag_upper;
            asid_hit[i] <= rdata[i].asid == cmp_asid;
            perms_valid[i] <= perms_valid_comb[i];
            //TODO: check if this should be combinational or sequential
            //hit_ohot[i] <= lower_tag_hit[i] & (upper_tag_hit[i] | rdata_superpage[i]) & (asid_hit[i] | rdata[i].globe);
        end
    end

    assign hit_ohot = upper_tag_hit & (lower_tag_hit | rdata_superpage) & (asid_hit | rdata_global);
    assign hit = |hit_ohot;

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

    //SFENCE
    logic sfence_valid_r;
    logic [$clog2(DEPTH)-1:0] flush_addr;
    logic [$clog2(DEPTH)-1:0] raddr_r;
    lfsr #(.WIDTH($clog2(DEPTH)), .NEEDS_RESET(0)) lfsr_counter (
        .en(1'b1),
        .value(flush_addr),
    .*);

    always_ff @(posedge clk) begin
        raddr_r <= tlb_raddr;
        sfence_valid_r <= sfence.valid; //Other SFENCE signals remain registered and do not need to be saved
    end

    assign tlb_waddr = sfence_valid_r ? raddr_r : mmu.virtual_address[12 +: $clog2(DEPTH)];
    always_comb begin
        if (sfence.valid)
            tlb_raddr = sfence.addr_only ? sfence.addr[12 +: $clog2(DEPTH)] : flush_addr;
        else
            tlb_raddr = tlb.virtual_address[12 +: $clog2(DEPTH)];
    end

    assign wdata_valid = ~sfence_valid_r;
    assign wdata = '{
        superpage : mmu.superpage,
        asid : asid,
        lower_tag : mmu.virtual_address[31-NONSUPERPAGE_W-:SUPERPAGE_W],
        upper_tag : mmu.virtual_address[31-:NONSUPERPAGE_W],
        ppn1 : mmu.upper_physical_address[19:10],
        ppn0 : mmu.upper_physical_address[9:0],
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
                3'b100: write[i] = 1'b1; //Clear everything
                3'b101: write[i] = ~rdata_global[i] & asid_hit[i]; //Clear non global for specified address space
                3'b110: write[i] = upper_tag_hit[i] & (lower_tag_hit[i] | rdata_superpage[i]); //Clear matching addresses
                3'b111: write[i] = (~rdata[i].globe & asid_hit[i]) & upper_tag_hit[i] & (lower_tag_hit[i] | rdata_superpage[i]); //Clear if both
                default: write[i] = mmu.write_entry & replacement_way[i];
            endcase
        end
    end

    //Permission fail
    logic perm_fail;
    assign perm_fail = |(hit_ohot & ~perms_valid) & translation_on;

    //Random replacement
    cycler #(.C_WIDTH(WAYS)) replacement_policy (       
        .en(1'b1), 
        .one_hot(replacement_way),
    .*);


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
    assign tlb.is_fault = mmu.is_fault | (new_request_r & perm_fail);


    always_comb begin
        tlb.physical_address[11:0] = mmu.virtual_address[11:0];
        if (~translation_on)
            tlb.physical_address[31:12] = mmu.virtual_address[31:12];
        else if (new_request_r) begin
            tlb.physical_address[31:22] = ppn1[hit_way];
            tlb.physical_address[21:12] = rdata_superpage[hit_way] ? mmu.virtual_address[21:12] : ppn0[hit_way];
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
        assert property (@(posedge clk) disable iff (rst) (new_request_r & translation_on & ~hit) |-> ~tlb.new_request)
        else $error("Request during miss in TLB!");

endmodule