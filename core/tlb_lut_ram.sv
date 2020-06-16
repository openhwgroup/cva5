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

import taiga_config::*;
import taiga_types::*;

module tlb_lut_ram #(
        parameter WAYS = 2,
        parameter DEPTH = 32
        )
        (
        input logic clk,
        input logic rst,
        input logic tlb_on,
        input logic [ASIDLEN-1:0] asid,
        mmu_interface.tlb mmu,
        tlb_interface.tlb tlb
        );

    localparam TLB_TAG_W = 32-12-$clog2(DEPTH);

    typedef struct packed {
        logic valid;
        logic [TLB_TAG_W-1:0] tag;
        logic [19:0] phys_addr;
    } tlb_entry_t;


    logic [$clog2(DEPTH)-1:0] tlb_read_addr;
    logic [$clog2(DEPTH)-1:0] tlb_write_addr;

    logic [TLB_TAG_W-1:0] virtual_tag;

    tlb_entry_t ram [DEPTH-1:0][WAYS-1:0];
    logic [DEPTH-1:0] valid [WAYS-1:0];

    logic [WAYS-1:0] tag_hit;
    logic [WAYS-1:0] replacement_way;

    logic [$bits(tlb_entry_t)-1:0] ram_data [WAYS-1:0][1];
    tlb_entry_t ram_entry [WAYS-1:0];
    tlb_entry_t new_entry;

    logic flush_in_progress;
    logic [$clog2(DEPTH)-1:0] flush_addr;

    logic hit;

    logic [WAYS-1:0] tlb_write;

    assign virtual_tag = tlb.virtual_address[31:32-TLB_TAG_W];
    assign tlb_read_addr = tlb.virtual_address[$clog2(DEPTH)+11:12];

    assign tlb_write_addr = tlb.flush ? flush_addr : tlb_read_addr;
    assign tlb_write = tlb.flush ? {WAYS{flush_in_progress}} : (replacement_way & {WAYS{mmu.write_entry}});

    assign new_entry.valid = ~tlb.flush;
    assign new_entry.tag = virtual_tag;
    assign new_entry.phys_addr = mmu.new_phys_addr;

    genvar i;
    generate
        for (i=0; i<WAYS; i=i+1) begin : lut_rams
            lut_ram #(.WIDTH($bits(tlb_entry_t)), .DEPTH(DEPTH), .READ_PORTS(1))
            ram_block (.clk(clk),
                    .waddr(tlb_write_addr), .ram_write(tlb_write[i]), .new_ram_data(new_entry),
                    .raddr({tlb_read_addr}), .ram_data_out(ram_data[i]));
            assign ram_entry[i] = ram_data[i][0];
        end
    endgenerate

    cycler #(.C_WIDTH(WAYS)) replacement_policy (.*, .en(1'b1), .one_hot(replacement_way));


    always_ff @ (posedge clk) begin
        if (rst)
            flush_in_progress <= 0;
        else if (tlb.flush_complete)
            flush_in_progress <= 0;
        else if (tlb.flush)
            flush_in_progress <= 1;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            flush_addr <= 0;
        else if (flush_in_progress)
            flush_addr <= flush_addr + 1;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            tlb.flush_complete <= 0;
        else
            tlb.flush_complete <= (flush_addr == (DEPTH-1));
    end


    always_comb begin
        for (int i=0; i<WAYS; i=i+1) begin
            tag_hit[i] = {ram_entry[i].valid, ram_entry[i].tag} == {1'b1, virtual_tag};
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            mmu.new_request <= 0;
        else if (mmu.write_entry)
            mmu.new_request <= 0;
        else if (tlb_on & ~hit & tlb.new_request)
            mmu.new_request <= 1;
    end

    assign mmu.virtual_address = tlb.virtual_address;
    assign mmu.execute = tlb.execute;
    assign mmu.rnw = tlb.rnw;

    assign hit = |tag_hit;
    assign tlb.complete = hit | ~tlb_on;

    always_comb begin
        tlb.physical_address[11:0] = tlb.virtual_address[11:0];
        tlb.physical_address[31:12] = tlb.virtual_address[31:12];
        for (int i=0; i<WAYS; i=i+1) begin
            if(tag_hit[i] & tlb_on)  tlb.physical_address[31:12] = ram_entry[i].phys_addr;
        end
    end


endmodule
