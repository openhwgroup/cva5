/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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

#ifndef CVA5Tracer_H
#define CVA5Tracer_H
#include <stdlib.h>
#include <iostream>
#include <iterator>
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vcva5_sim.h"
#include "SimMem.h"
#include "AXI_DDR_simulation/axi_ddr_sim.h"
//#define TRACE_ON

#define COMPLIANCE_SIG_PHASE_NOP 0x00B00013U
#define BENCHMARK_START_COLLECTION_NOP 0x00C00013U
#define BENCHMARK_END_COLLECTION_NOP 0x00D00013U
#define BENCHMARK_RESUME_COLLECTION_NOP 0x00E00013U
#define ERROR_TERMINATION_NOP 0x00F00013U
#define SUCCESS_TERMINATION_NOP 0x00A00013U

template <typename T, int N>
constexpr int arraySize(T(&)[N]) { return N; }

static const char * const eventNames[] = {
    "early_branch_correction",
    "operand_stall",
    "unit_stall",
    "no_id_stall",
    "no_instruction_stall",
    "other_stall",
    "instruction_issued_dec",
    "branch_operand_stall",
    "alu_operand_stall",
    "ls_operand_stall",
    "div_operand_stall",
    "alu_op",
    "branch_or_jump_op",
    "load_op",
    "store_op",
    "mul_op",
    "div_op",
    "misc_op",
    "branch_correct",
    "branch_misspredict",
    "return_correct",
    "return_misspredict",
    "load_conflict_delay",
    "rs1_forwarding_needed",
    "rs2_forwarding_needed",
    "rs1_and_rs2_forwarding_needed"
};
static const int numEvents = arraySize(eventNames);

//Testbench with CVA5 trace outputs on toplevel
class CVA5Tracer {
public:
  CVA5Tracer(std::ifstream& programFile);
  ~CVA5Tracer();
  bool check_if_instruction_retired(uint32_t instruction);
  bool has_terminated();
  bool has_stalled();
  bool store_queue_empty();
  void print_stats();
  void reset_stats();
  void reset();
  void tick();

  void set_log_file(std::ofstream* logFile);
  void set_pc_file(std::ofstream* pcFile);
  void start_tracer(const char *trace_file);
  uint64_t get_cycle_count();

  //DDR Simulation
  Vcva5_sim *tb;
private:
  axi_ddr_sim * axi_ddr;
  SimMem *mem;
#ifdef TRACE_ON
		VerilatedVcdC	*verilatorWaveformTracer;
#endif
  std::ofstream* logFile;
  std::ofstream* pcFile;
  bool logPC = false;

  int reset_length = 64;
  int stall_limit = 2000;
  int stall_count = 0;
  uint64_t cycle_count = 0;
  uint64_t event_counters[numEvents];

  bool collect_stats = false;
  bool program_complete = false;

  void update_stats();
  void update_UART();
  void update_memory();
  uint32_t instruction_r;
  uint32_t data_out_r;

};
#endif
