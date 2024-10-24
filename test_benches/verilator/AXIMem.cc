/*
 * Copyright © 2024 Chris Keilbart
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
 *             Chris Keilbart <ckeilbar@sfu.ca>
 */

#include <fstream>
#include <algorithm>
#include <cstring>
#include "verilated.h"
#include "Vcva5_sim.h"
#include "AXIMem.h"

static_assert(MEM_WORDS >= 1 && MEM_WORDS <= 16, "Bus width must be 32-512");
//No other assertions, this unit can handle any compliant master (but does not check for compliance)

//TODO: ~0 is used to mark invalid data, but 1 for invalid IDs because Verilator cannot handle set MSBs

unsigned AXIMem::log2(unsigned x) {
    unsigned y = 0;
    while (x) {
        x >>= 1;
        y++;
    }
    return y - 1;
}

AXIMem::AXIMem(Vcva5_sim* tb){
    this->tb = tb;
    //Static casting for safety is an alternative
    rdata_pointer = (uint32_t*) &tb->ddr_axi_rdata;
    wdata_pointer = (uint32_t*) &tb->ddr_axi_wdata;

    //Create the delay distributions
    generator = default_random_engine(seed);
    rvalid_geo = geometric_distribution<unsigned>(rvalid_distribution_p);
    bvalid_geo = geometric_distribution<unsigned>(bvalid_distribution_p);
    arready_bern = bernoulli_distribution(arready_p);
    awready_bern = bernoulli_distribution(awready_p);
    wready_bern = bernoulli_distribution(wready_p);
    rvalid_bern = bernoulli_distribution(rvalid_p);

    rst();
}

AXIMem::AXIMem(ifstream (&memFiles)[NUM_CORES], Vcva5_sim* tb) : AXIMem(tb) {

    uint32_t line_bin;
    string line_hex;
    uint32_t addr;
    const uint32_t addr_mask = (MEM_WORDS-1) << 2;

    //First iterate over cores
    for (int i = 0; i < NUM_CORES; i++) {
        addr = (STARTING_ADDR + i*PROGRAM_SPACING);

        //Hex files have one 32 bit hexadecimal number per line, we check the first line to determine file type
        getline(memFiles[i], line_hex);
        bool fileIsHex = line_hex.size() == 8;
        try {
            stoul(line_hex, 0, 16);
        }
        catch (invalid_argument& ex) {
            fileIsHex = false;
        }
        memFiles[i].clear();
        memFiles[i].seekg(0, ios::beg);

        //Then iterate over pages
        while (!memFiles[i].eof()) {
            if (fileIsHex) {
                getline(memFiles[i], line_hex);
                line_bin = stoul(line_hex, 0, 16);
            }
            else
                memFiles[i].read((char*) &line_bin, 4);

            uint32_t masked_addr = addr & addr_mask;
            uint32_t* rdata;
            try {
                rdata = mem.at(addr >> ADDR_SHIFT_AMT);
            } catch (out_of_range ex) {
                rdata = new uint32_t[MEM_WORDS];
                memset(rdata, 0, 4*MEM_WORDS);
                mem[addr >> ADDR_SHIFT_AMT] = rdata;
            }
            rdata[masked_addr>>2] = line_bin;
            
            addr += 4;
        }
    }
}

inline void AXIMem::pre_ar() {
    tb->ddr_axi_arready = 0;

    //Randomly deny a request
    if (arready_bern(generator))
        return;
    
    for (unsigned i = 0; i < max_read_requests; i++)
        if (!inflight_r[i].valid) {
            tb->ddr_axi_arready = 1;
            return;
        }
}

inline void AXIMem::post_ar() {
    if (!tb->ddr_axi_arvalid || !tb->ddr_axi_arready)
        return;
    
    unsigned free_index;
    unsigned max_id_latency = 0;
    for (int i = max_read_requests-1; i >= 0; i--) {
        if (!inflight_r[i].valid) //Searching backwards means insertions are likely at the beginning
            free_index = i;
        else if (inflight_r[i].id == tb->ddr_axi_arid)
            max_id_latency = max(max_id_latency, inflight_r[i].remaining);
    }

    inflight_r[free_index].address = tb->ddr_axi_araddr;
    inflight_r[free_index].id = tb->ddr_axi_arid;
    inflight_r[free_index].burst = tb->ddr_axi_arburst;
    inflight_r[free_index].size = tb->ddr_axi_arsize;
    inflight_r[free_index].length = tb->ddr_axi_arlen;
    //Need to set the latency above the latency of the maximum outstanding request with the same ID (for ordering)
    inflight_r[free_index].remaining = max(rvalid_min_latency + rvalid_geo(generator), max_id_latency+1);
    inflight_r[free_index].valid = true;
}

inline void AXIMem::rst_ar() {
    tb->ddr_axi_arready = 0;

    arready_bern.reset();
    rvalid_geo.reset();
    for (unsigned i = 0; i < max_read_requests; i++)
        inflight_r[i].valid = false;
}

inline void AXIMem::pre_aw() {
    tb->ddr_axi_awready = 0;

    //Randomly deny a request
    if (awready_bern(generator))
        return;
    
    for (unsigned i = 0; i < max_write_requests; i++) {
        if (!inflight_w[i].valid) {
            tb->ddr_axi_awready = 1;
            return;
        }
    }
}

inline void AXIMem::post_aw() {
    if (!tb->ddr_axi_awvalid || !tb->ddr_axi_awready)
        return;
    
    unsigned free_index;
    unsigned max_id_latency;
    for (int i = max_write_requests-1; i >= 0; i--) {
        if (!inflight_w[i].valid) //Searching backwards means insertions are likely at the beginning
            free_index = i;
        else if (inflight_w[i].id == tb->ddr_axi_awid)
            max_id_latency = max(max_id_latency, inflight_w[i].remaining);
    }

    w_queue.push(free_index);
    inflight_w[free_index].address = tb->ddr_axi_awaddr;
    inflight_w[free_index].id = tb->ddr_axi_awid;
    inflight_w[free_index].burst = tb->ddr_axi_awburst;
    inflight_w[free_index].size = tb->ddr_axi_awsize;
    inflight_w[free_index].length = tb->ddr_axi_awlen;
    inflight_w[free_index].remaining = 0;
    inflight_w[free_index].valid = true;
}

inline void AXIMem::rst_aw() {
    tb->ddr_axi_awready = 0;

    awready_bern.reset();
    for (unsigned i = 0; i < max_write_requests; i++)
        inflight_w[i].valid = false;
}

inline void AXIMem::pre_w() {
    tb->ddr_axi_wready = !wready_bern(generator) && !w_queue.empty();
}

inline void AXIMem::post_w() {
    //Place the wdata in a queue for future commitment
    if (tb->ddr_axi_wvalid && tb->ddr_axi_wready) {
        const unsigned current_id = w_queue.front();
        wdata_entry new_entry;
        memcpy(new_entry.data, wdata_pointer, 4*MEM_WORDS);
        new_entry.strb = tb->ddr_axi_wstrb;
        inflight_wdata[current_id].push(new_entry);

        if (tb->ddr_axi_wlast) {
            unsigned max_id_latency = 0;
            for (unsigned i = 0; i < max_write_requests; i++) {
                if (inflight_w[i].valid && inflight_w[i].id == current_id)
                    max_id_latency = max(max_id_latency, inflight_w[i].remaining);
            }

            inflight_w[current_id].remaining = max(bvalid_min_latency + bvalid_geo(generator), max_id_latency+1);
            w_queue.pop();
        }
    }

    //Decrement outstanding write latencies and commit finished outstanding writes
    for (int i = max_write_requests-1; i >= 0; i--) { //Go backwards because that makes it more likely to reorder requests
        //0 remaining indicates a request that is waiting for wdata
        if (!inflight_w[i].valid || inflight_w[i].remaining == 0)
            continue;

        if (--inflight_w[i].remaining != 0)
            continue;
            
        //Commit
        b_queue.push(i);
        uint32_t raw_addr = inflight_w[i].address;
        const unsigned burst = inflight_w[i].burst;
        const unsigned size_bytes = 1 << inflight_w[i].size;
        const uint32_t line_bytes = size_bytes*(inflight_w[i].length+1);
        const uint32_t mask = ~0 << log2(line_bytes);
        
        while (!inflight_wdata[i].empty()) {
            //Do the write
            uint8_t* rdata;
            try {
                rdata = (uint8_t*) mem.at(raw_addr >> ADDR_SHIFT_AMT);
            } catch (out_of_range ex) {
                rdata = (uint8_t*) new uint32_t[MEM_WORDS];
                memset(rdata, 0, 4*MEM_WORDS);
                mem[raw_addr >> ADDR_SHIFT_AMT] = (uint32_t*) rdata;
            }
            uint8_t* wdata = (uint8_t*) inflight_wdata[i].front().data;
            uint64_t strb = inflight_wdata[i].front().strb;

            for (unsigned j = 0; j < 4*MEM_WORDS; j++) {
                if (strb & 1)
                    *rdata = *wdata;
                wdata++;
                rdata++;
                strb >>= 1;
            }

            inflight_wdata[i].pop();

            //Set up the address for the next go
            if (burst == 1) //INCR
                raw_addr += size_bytes;
            else if (burst == 2) //WRAP
                raw_addr = (mask & raw_addr) | (~mask & raw_addr+size_bytes);
        }
    }
}

void AXIMem::rst_w() {
    tb->ddr_axi_wready = 0;

    bvalid_geo.reset();
    wready_bern.reset();
    while (!w_queue.empty())
        w_queue.pop();
    
    for (unsigned i = 0; i < max_write_requests; i++)
        while (!inflight_wdata[i].empty())
            inflight_wdata[i].pop();
}

void AXIMem::pre_r() {
    if (rvalid_bern(generator) || r_queue.empty()) {
        tb->ddr_axi_rvalid = 0;
        tb->ddr_axi_rlast = 0;
        tb->ddr_axi_rid = 1; //Cannot use ~0
        memset(rdata_pointer, ~0, 4*MEM_WORDS);
        return;
    }
    
    const unsigned current_id = r_queue.front();
    tb->ddr_axi_rvalid = 1;
    tb->ddr_axi_rid = inflight_r[current_id].id;
    tb->ddr_axi_rlast = read_burst_count == inflight_r[current_id].length;

    uint32_t start_addr = inflight_r[current_id].address;
    const unsigned burst = inflight_r[current_id].burst;
    const unsigned size_bytes = 1 << inflight_r[current_id].size;
    
    if (burst == 1) //INCR
        start_addr += read_burst_count*size_bytes;
    else if (burst == 2) { //WRAP
        const uint32_t line_bytes = size_bytes*(inflight_r[current_id].length+1);
        const uint32_t mask = ~0 << log2(line_bytes);
        start_addr = (mask & start_addr) | (~mask & start_addr+read_burst_count*size_bytes);
    }

    uint32_t* rdata;
    try {
        rdata = mem.at(start_addr >> ADDR_SHIFT_AMT);
    } catch (out_of_range ex) {
        rdata = new uint32_t[MEM_WORDS];
        memset(rdata, 0, 4*MEM_WORDS);
        mem[start_addr >> ADDR_SHIFT_AMT] = rdata;
    }
    memcpy(rdata_pointer, rdata, 4*MEM_WORDS);
}

void AXIMem::post_r() {
    //Handle the last read
    if (tb->ddr_axi_rready && tb->ddr_axi_rvalid) {
        if (tb->ddr_axi_rlast) {
            read_burst_count = 0;
            inflight_r[r_queue.front()].valid = false;
            r_queue.pop();
        }
        else
            read_burst_count++;
    }

    //Commit a read
    for (int i = max_read_requests-1; i >= 0; i--) { //Go backwards because that makes it more likely to reorder requests
        if (!inflight_r[i].valid || !inflight_r[i].remaining)
            continue;
        if (!--inflight_r[i].remaining)
            r_queue.push(i);    
    }
}

void AXIMem::rst_r() {
    read_burst_count = 0;
    tb->ddr_axi_rvalid = 0;
    tb->ddr_axi_rresp = 0; //Always good
    tb->ddr_axi_rlast = 0;
    tb->ddr_axi_rid = 1; //Cannot use ~0
    memset(rdata_pointer, ~0, 4*MEM_WORDS);

    while (!r_queue.empty())
        r_queue.pop();
}

void AXIMem::pre_b() {
    bool valid = !b_queue.empty();
    tb->ddr_axi_bvalid = valid;
    tb->ddr_axi_bid = valid ? inflight_w[b_queue.front()].id : 1; //Cannot use ~0
}

void AXIMem::post_b() {
    if (tb->ddr_axi_bvalid && tb->ddr_axi_bready) {
        inflight_w[b_queue.front()].valid = false;
        b_queue.pop();
    }
}

void AXIMem::rst_b() {
    tb->ddr_axi_bid = 0;
    tb->ddr_axi_bresp = 0; //Always good
    tb->ddr_axi_bvalid = 0;
    while (!b_queue.empty())
        b_queue.pop();
}

void AXIMem::rst() {
    //Order does not matter
    rst_ar();
    rst_aw();
    rst_r();
    rst_w();
    rst_b();

}

void AXIMem::pre() {
    if (tb->rst)
        rst();
    else {
        pre_ar();
        pre_aw();
        pre_w();
        pre_r();
        pre_b();
    }
}

void AXIMem::post() {
    post_ar();
    post_r();
    post_aw();
    post_w();
    post_b();
}

AXIMem::~AXIMem() {
    for (auto it = mem.begin(); it != mem.end(); it++)
        delete[] it->second;
}