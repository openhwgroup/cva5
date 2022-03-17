#include <sstream>
#include <string>
#include <fstream>
#include <iostream>
#include "SimMem.h"
#include <iomanip>


SimMem::SimMem(std::ifstream& program, uint32_t mem_size) : mem_size(mem_size) {
    //static uint32_t SimMem::memory1;
    //static uint32_t SimMem::memory2;
    memory1 = new uint32_t[mem_size*256]();//mem_size in KB
    memory2 = new uint32_t[mem_size*256]();//mem_size in KB
    address_mask = (mem_size*256) - 1; //mask to prevent any out-of-bounds array access.  Assumes power-of-two memory size
    std::cout << std::hex << address_mask << std::dec << std::endl;

    std::string line;
    for (int i =0; (i < mem_size*256) && (std::getline(program, line)); i++) {
        memory1[i] = std::stoul(line, 0, 16);
        std::getline(program, line);
        memory2[i] = std::stoul(line, 0, 16);
    }
    mem_counter = 0;

    mem_concat = memory1[8066];
    mem_concat = mem_concat << 32 | memory2[8066];

}

uint32_t SimMem::read_instruction(uint32_t addr) {
    uint32_t we = addr & 0x1; //extract word select bit
    uint32_t new_addr = addr >> 1;

    if (we) {
        //std::cout << std::hex << "addr: 0x" << addr << "\tnew_addr: 0x" << new_addr << "\tinst@" << (new_addr&address_mask) << ": 0x" << memory2[new_addr & address_mask] << " \n";
        return memory2[new_addr & address_mask];
    }
    else {
        //std::cout << std::hex << "addr: 0x" << addr << "\tnew_addr: 0x" << new_addr << "\tinst@" << (new_addr&address_mask) << ": 0x" << memory1[new_addr & address_mask] << " \n";
        return memory1[new_addr & address_mask];
    }
}

uint64_t SimMem::read(uint32_t addr) {
    uint32_t data1 = memory1[addr & address_mask];
    uint32_t data2 = memory2[addr & address_mask];
    return ((uint64_t(data1) << 32) | data2);
}

void SimMem::write(uint32_t addr, uint64_t data, uint32_t be, uint32_t we) {
    uint32_t write_mask, old_word1, old_word2; 
    uint32_t data2 = uint32_t(data);            //lower 32 bits 
    uint32_t data1 = uint32_t(data >> 32);      //upper 32 bits 
 
    write_mask = 0;
    if (be & 0x1)
        write_mask |= 0x000000FFL;
    if (be & 0x2)
        write_mask |= 0x0000FF00L;
    if (be & 0x4)
        write_mask |= 0x00FF0000L;
    if (be & 0x8)
        write_mask |= 0xFF000000L;

    if (we == 0) {
        //integer bank1
        old_word1 = memory1[addr & address_mask];
        memory1[addr & address_mask] = (old_word1 & ~write_mask) | (data2 & write_mask);
    } else if (we == 1) {
        //integer bank2
        old_word2 = memory2[addr & address_mask];
        memory2[addr & address_mask] = (old_word2 & ~write_mask) | (data2 & write_mask);
    } else if (we == 2) {
        //double bank1 and bank2
        old_word1 = memory1[addr & address_mask];
        old_word2 = memory2[addr & address_mask];
        memory1[addr & address_mask] = (old_word1 & ~write_mask) | (data1 & write_mask);
        memory2[addr & address_mask] = (old_word2 & ~write_mask) | (data2 & write_mask);
    }
    //if ((addr & address_mask) == 8066){
        //std::cout << "instruction mem modified - addr: 0x" << addr << "\tdata: " << data << std::endl;
    //}
}

void SimMem::printMem(std::string logfile) {
    std::ofstream mem_log;
    mem_log.open(logfile, std::ofstream::trunc);
    for (int i =0; (i < mem_size*256); i++) {
        //std::cout << std::hex << "0x" << std::setw(8) << std::setfill('0') << i << 
        mem_log << std::hex << "0x" << std::setw(8) << std::setfill('0') << i << 
        " " << std::setw(8) << std::setfill('0') << memory1[i] << " " <<
               std::setw(8) << std::setfill('0') << memory2[i] << std::endl;
    }
    mem_log.close();
}

void SimMem::printMemLoca(uint32_t addr){
    std::cout << std::hex << "0x" << std::setw(8) << std::setfill('0') << addr << 
        " " << std::setw(8) << std::setfill('0') << memory1[addr & address_mask] << " " <<
               std::setw(8) << std::setfill('0') << memory2[addr & address_mask] << std::endl;
}

int SimMem::mem_modified(uint32_t addr) { //the addr is the actual addr in the memory arrays (lower 3 bits discarded and masked)
    if (memory1[addr]!=0xfc010113 | memory2[addr]!=0x1a00793){
        std::cout << "instruction memory modified: 0x";
        return 1;
    }
    return 0;
}

uint64_t SimMem::get_mem(uint32_t addr) {//the addr is the actual addr in the memory arrays (lower 3 bits discarded and masked)
    uint64_t mem_concat = memory1[addr];
    mem_concat = mem_concat << 32 | memory2[addr];
    return mem_concat;
}

SimMem::~SimMem() {
    delete[] memory1;
    delete[] memory2;
}
