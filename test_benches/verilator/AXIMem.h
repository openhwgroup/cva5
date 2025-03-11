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

#ifndef AXIDDR_H
#define AXIDDR_H
#include <queue>
#include <unordered_map>
#include <random>
#include <cstdint>
#include "Vcva5_sim.h"

using namespace std;

//Default defines; can be overridden by command line
#ifndef NUM_CORES
#define NUM_CORES 1
#endif
#ifndef STARTING_ADDR
#define STARTING_ADDR 0x80000000
#endif
#ifndef PROGRAM_SPACING
#define PROGRAM_SPACING 0x04000000
#endif

//If DETERMINISTIC is set, randomness effecting memory performance is disabled
#if defined(DETERMINISTIC) && DETERMINISTIC != 0
#define RVALID_DISTRIBUTION_P 0.0
#define BVALID_DISTRIBUTION_P 0.0
#define ARREADY_P 0.0
#define AWREADY_P 0.0
#define WREADY_P 0.0
#define RVALID_P 0.0
#else
#define RVALID_DISTRIBUTION_P 0.5
#define BVALID_DISTRIBUTION_P 0.5
#define ARREADY_P 0.25
#define AWREADY_P 0.25
#define WREADY_P 0.1
#define RVALID_P 0.1
#endif

//Shared RNG and simulation properties
#define RNG_SEED 101099
#define RVALID_MIN_LATENCY 20
#define BVALID_MIN_LATENCY 25
#define MAX_READS 8
#define MAX_WRITES 8

//Certain logic depends on the width of the data bus
#define MEM_TYPE decltype(*Vcva5_sim::ddr_axi_rdata)
#define MEM_WORDS (8*sizeof(Vcva5_sim::ddr_axi_rdata)/32)
#define ADDR_SHIFT_AMT (log2(MEM_WORDS)+2)

struct request {
    uint32_t address;
    unsigned id;
    unsigned burst;
    unsigned size;
    unsigned length;
    unsigned remaining;
    bool valid;
};

struct wdata_entry {
    uint32_t data[MEM_WORDS];
    uint64_t strb; //This caps the bus size to 512
};

class AXIMem {
public:
    //Initialize DDR
    AXIMem(ifstream (&memFiles)[NUM_CORES], Vcva5_sim* tb);
    //Free the memory map
    ~AXIMem();

    //Set outputs
    void pre();
    //Respond to inputs
    void post();

private:
    //Basic initialization that doesn't construct the memory itself
    AXIMem(Vcva5_sim* tb);

    inline void pre_ar();
    inline void pre_aw();
    inline void pre_r();
    inline void pre_w();
    inline void pre_b();
    inline void post_ar();
    inline void post_aw();
    inline void post_r();
    inline void post_w();
    inline void post_b();
    void rst();
    inline void rst_ar();
    inline void rst_aw();
    inline void rst_r();
    inline void rst_w();
    inline void rst_b();

    unsigned log2(unsigned x);

    //Simulation tuneables
    //Latencies follow a shifted geometric distribution
    const unsigned seed = RNG_SEED;
    const unsigned rvalid_min_latency = RVALID_MIN_LATENCY;
    const unsigned bvalid_min_latency = BVALID_MIN_LATENCY;
    const double rvalid_distribution_p = RVALID_DISTRIBUTION_P;
    const double bvalid_distribution_p = BVALID_DISTRIBUTION_P;

    //Bus availability
    static const unsigned max_read_requests = MAX_READS;
    static const unsigned max_write_requests = MAX_WRITES;

    //Odds that it won't be available on any given cycle
    const double arready_p = ARREADY_P;
    const double awready_p = AWREADY_P;
    const double wready_p = WREADY_P;
    const double rvalid_p = RVALID_P;

    //Latency Randomizers
    default_random_engine generator;
    geometric_distribution<unsigned> rvalid_geo;
    geometric_distribution<unsigned> bvalid_geo;
    bernoulli_distribution arready_bern;
    bernoulli_distribution awready_bern;
    bernoulli_distribution wready_bern;
    bernoulli_distribution rvalid_bern;

    //Pointers to Data
    Vcva5_sim *tb;
    uint32_t* wdata_pointer;
    uint32_t* rdata_pointer;
    unordered_map<uint32_t,uint32_t*> mem; //TODO: use the gross fixed array length syntax
    request inflight_r[max_read_requests];
    request inflight_w[max_write_requests];
    queue<wdata_entry> inflight_wdata[max_write_requests];
    queue<unsigned> w_queue;
    queue<unsigned> b_queue;
    queue<unsigned> r_queue;
    unsigned read_burst_count;

};

#endif