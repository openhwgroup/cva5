#include <sstream>
#include <string>
#include <fstream>
#include <iostream>
#include "SimMem.h"



SimMem::SimMem(std::ifstream& program, uint32_t mem_size) : mem_size(mem_size) {
    memory = new uint32_t[mem_size*256]();//mem_size in KB
    address_mask = (mem_size*256) - 1; //mask to prevent any out-of-bounds array access.  Assumes power-of-two memory size

    std::string line;
    for (int i =0; (i < mem_size*256) && (std::getline(program, line)); i++) {
        memory[i] = std::stoul(line, 0, 16);
    }

}

uint32_t SimMem::read(uint32_t addr) {
    return memory[addr & address_mask];
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

    old_word = memory[addr & address_mask];
    memory[addr & address_mask] = (old_word & ~write_mask) | (data & write_mask);
}

SimMem::~SimMem() {
    delete[] memory;
}
