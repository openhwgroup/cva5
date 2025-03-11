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

#include <iostream>
#include <iomanip>
#include <cstring>
#include "SimMem.h"

using namespace std;

//Support files in hex or raw binary form
SimMem::SimMem(ifstream (&memFiles)[NUM_CORES]) {
    string line_hex;
    uint32_t addr;
    uint32_t line_bin;

    for (int i = 0; i < NUM_CORES; i++) {
        addr = (STARTING_ADDR + i*PROGRAM_SPACING) >> 2; //Only handle 32b memory words

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

            memory[addr++] = line_bin;
        }
    }
}

uint32_t SimMem::read(uint32_t addr) {
    return memory[addr]; //Will insert 0 if not present
}

void SimMem::write(uint32_t addr, uint32_t data, uint32_t be) {
    uint32_t write_mask, old_word;

    write_mask = 0;

    if (be & 0x1)
        write_mask |= 0x000000FFL;
    if (be & 0x2)
        write_mask |= 0x0000FF00L;
    if (be & 0x4)
        write_mask |= 0x00FF0000L;
    if (be & 0x8)
        write_mask |= 0xFF000000L;

    old_word = memory[addr]; //Will insert 0 if not present
    memory[addr] = (old_word & ~write_mask) | (data & write_mask);
}
