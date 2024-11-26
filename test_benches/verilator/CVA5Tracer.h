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

#ifndef CVA5Tracer_H
#define CVA5Tracer_H
#include <stdlib.h>
#include <iostream>
#include <iterator>
#include "verilated.h"
#include "verilated_fst_c.h"
#include "Vcva5_sim.h"
#include "SimMem.h"
#include "AXIMem.h"
//#define TRACE_ON

#define COMPLIANCE_SIG_PHASE_NOP 0x00B00013U
#define BENCHMARK_START_COLLECTION_NOP 0x00C00013U
#define BENCHMARK_END_COLLECTION_NOP 0x00D00013U
#define BENCHMARK_RESUME_COLLECTION_NOP 0x00E00013U
#define ERROR_TERMINATION_NOP 0x00F00013U
#define SUCCESS_TERMINATION_NOP 0x00A00013U

//Testbench with CVA5 trace outputs on toplevel
class CVA5Tracer {
public:
  CVA5Tracer(std::ifstream (&programFile)[1]);
  ~CVA5Tracer();
  bool check_if_instruction_retired(uint32_t instruction);
  bool has_terminated();
  bool has_stalled();
  bool store_queue_empty();
  void reset();
  void tick();

  void set_log_file(std::ofstream* logFile);
  void set_pc_file(std::ofstream* pcFile);
  void start_tracer(const char *trace_file);
  static uint64_t get_cycle_count();

  //DDR Simulation
  Vcva5_sim *tb;
private:
  AXIMem *axi_ddr;
  SimMem *mem;
#ifdef TRACE_ON
  VerilatedFstC* verilatorWaveformTracer;
#endif
  std::ofstream* logFile;
  std::ofstream* pcFile;
  bool logPC = false;

  int reset_length = 64;
  int stall_limit = 2000;
  int stall_count = 0;
  static uint64_t cycle_count;

  bool program_complete = false;

  void update_UART();
  void memory_pre();
  void memory_post();
  uint32_t instruction_r;
  uint32_t data_out_r;
};
#endif
