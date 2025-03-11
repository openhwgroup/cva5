/*
 * Copyright © 2019 Eric Matthews, Chris Keilbart, Lesley Shannon
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

#ifndef SIMMEM_H
#define SIMMEM_H
#include <fstream>
#include <unordered_map>
#include <queue>
#include <cstdint>

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

class SimMem {
public:
    SimMem(ifstream (&memFiles)[NUM_CORES]);
    void write(uint32_t addr, uint32_t data, uint32_t be);
    uint32_t read(uint32_t addr);
private:
    queue<uint32_t> i_queue[NUM_CORES];
    queue<uint32_t> d_queue[NUM_CORES];
    unordered_map<uint32_t,uint32_t> memory;
};
#endif
