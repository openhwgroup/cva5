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
#include "CVA5Tracer.h"

//#define TRACE_ON

bool CVA5Tracer::check_if_instruction_retired(uint32_t instruction) {
    bool result = false;
    for (int i =0; i < tb->NUM_RETIRE_PORTS; i++) {
        result |= (tb->retire_ports_instruction[i] == instruction) && tb->retire_ports_valid[i];
    }
    return result;
}


bool CVA5Tracer::has_terminated() {

    if (check_if_instruction_retired(ERROR_TERMINATION_NOP)) {
        std::cout << "\n\nError!!!!\n\n";
        return true;
    }
    //Custom nop for regular termination
    program_complete |= check_if_instruction_retired(SUCCESS_TERMINATION_NOP);

    if (program_complete && tb->store_queue_empty)
        return true;

    return false;
}


bool CVA5Tracer::has_stalled() {
    if (!tb->retire_ports_valid[0]) {
        if (stall_count > stall_limit) {
            stall_count = 0;
            std::cout << "\n\nError!!!!\n";
            std::cout << "Stall of " << stall_limit << " cycles detected!\n\n";
            return true;
        } else {
            stall_count++;
        }
    }
    else 
        stall_count=0;
    return false;
}

bool CVA5Tracer::store_queue_empty() {
    return tb->store_queue_empty;
}

void CVA5Tracer::reset() {
    tb->clk = 0;
    tb->rst = 1;
    for (int i=0; i < reset_length; i++)
        tick();

    tb->rst = 0;
}

void CVA5Tracer::set_log_file(std::ofstream* logFile) {
    this->logFile = logFile;
}
void CVA5Tracer::set_pc_file(std::ofstream* pcFile) {
    this->pcFile = pcFile;
    logPC = true;
}

void CVA5Tracer::update_UART() {
    if (tb->write_uart) {
        std::cout <<  tb->uart_byte << std::flush;
        *logFile << tb->uart_byte;
    }
}

void CVA5Tracer::memory_pre() {
    tb->instruction_bram_data_out = instruction_r;
    tb->data_bram_data_out = data_out_r;
}

void CVA5Tracer::memory_post() {
    if (tb->instruction_bram_en)
        instruction_r = mem->read(tb->instruction_bram_addr);
    if (tb->data_bram_en) {
        data_out_r = mem->read(tb->data_bram_addr);
        mem->write(tb->data_bram_addr, tb->data_bram_data_in, tb->data_bram_be);
    }

}

void CVA5Tracer::tick() {
    //Rising edge
    cycle_count++;
    tb->clk = 1;
    tb->eval();

    //Set outputs
    axi_ddr->pre();
    memory_pre();
    tb->eval();

    //Respond to inputs
    axi_ddr->post();
    memory_post();

    #ifdef TRACE_ON
        verilatorWaveformTracer->dump(vluint32_t(cycle_count));
    #endif

    update_UART();
    #ifdef PC_TRACE_ON
        for (int i =0; i < tb->NUM_RETIRE_PORTS; i++) {
            if (logPC && tb->retire_ports_valid[i]) {
                *pcFile << std::hex << tb->retire_ports_pc[i] << std::endl;
            }
        }
    #endif

    //Falling edge
    cycle_count++;
    tb->clk = 0;
    tb->eval();
    #ifdef TRACE_ON
        verilatorWaveformTracer->dump(vluint32_t(cycle_count));
    #endif
}

void CVA5Tracer::start_tracer(const char *trace_file) {
    #ifdef TRACE_ON
        verilatorWaveformTracer = new VerilatedFstC;
        tb->trace(verilatorWaveformTracer, 99);
        verilatorWaveformTracer->open(trace_file);
    #endif
}

uint64_t CVA5Tracer::cycle_count = 0;
uint64_t CVA5Tracer::get_cycle_count() {
    return cycle_count;
}

CVA5Tracer::CVA5Tracer(std::ifstream (&programFile)[1]) {
    cycle_count = 0;

    #ifdef TRACE_ON
        Verilated::traceEverOn(true);
    #endif

    tb = new Vcva5_sim;
    
    axi_ddr = new AXIMem(programFile, tb);
    programFile[0].clear();
    programFile[0].seekg(0, ios::beg);
    mem = new SimMem(programFile);

    instruction_r = mem->read(tb->instruction_bram_addr);
    data_out_r = 0;
}


CVA5Tracer::~CVA5Tracer() {
    #ifdef TRACE_ON
        verilatorWaveformTracer->flush();
        verilatorWaveformTracer->close();
    #endif
    delete mem;
    delete axi_ddr;
    delete tb;
}
