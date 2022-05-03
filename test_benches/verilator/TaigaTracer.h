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

#ifndef TaigaTracer_H
#define TaigaTracer_H
#include <stdlib.h>
#include <iostream>
#include <iterator>
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vtaiga_sim.h"
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

static const char * const fp_eventNames[] = {
        "fp_instruction_issued_dec",
        "fp_operand_stall",
        "fp_unit_stall",
        "fp_no_id_stall",
        "fp_no_instruction_stall",
        "fp_other_stall",
        "fls_operand_stall",
        "fmadd_operand_stall",
        "fadd_operand_stall",
        "fmul_operand_stall",
        "fdiv_operand_stall",
        "fsqrt_operand_stall",
        "fcmp_operand_stall",
        "fsign_inject_operand_stall",
        "fclass_operand_stall",
        "fcvt_operand_stall",
        "fp_load_op",
        "fp_store_op",
        "fp_fmadd_op",
        "fp_add_op",
        "fp_mul_op",
        "fp_div_op",
        "fp_sqrt_op",
        "fp_cvt_op",
        "fp_cmp_op",
        "fp_minmax_op",
        "fp_class_op",
        "fp_sign_inject_op",
        "operand_stall_due_to_fls",
        "operand_stall_due_to_fmadd",
        "operand_stall_due_to_fdiv_sqrt",
        "operand_stall_due_to_wb2fp",
        "fmadd_wb_stall",
        "fmul_wb_stall",
        "fdiv_sqrt_wb_stall",
        "wb2fp_wb_stall",
        "fmadd_stall_due_to_fmadd",
        "fmadd_operand_stall_rs1",
        "fmadd_operand_stall_rs2",
        "fmadd_operand_stall_rs3",
        "fadd_operand_stall_rs1",
        "fadd_operand_stall_rs2",
        "fmul_operand_stall_rs1",
        "fmul_operand_stall_rs2",
        "fadd_stall_due_to_fmadd",
        "rs1_subnormal",
        "rs2_subnormal",
        "rs3_subnormal"
};

static const char * const LargeTraceSigsNames[] = {
        "inflight_count"
};

static const int numEvents = arraySize(eventNames);
static const int fp_numEvents = arraySize(fp_eventNames);
static const int num_LargeTraceSigs = arraySize(LargeTraceSigsNames);

//Testbench with Taiga trace outputs on toplevel
class TaigaTracer {
public:
  TaigaTracer(std::ifstream& programFile);
  ~TaigaTracer();
  bool check_if_instruction_retired(uint32_t instruction);
  bool has_terminated();
  bool has_stalled();
  bool store_queue_empty();
  void print_stats();
  void reset_stats();
  void reset();
  void tick();

  void set_log_file(std::ofstream* logFile);
  void start_tracer(const char *trace_file);
  uint64_t get_cycle_count();

  //DDR Simulation
  Vtaiga_sim *tb;
private:
  axi_ddr_sim * axi_ddr;
  SimMem *mem;
#ifdef TRACE_ON
		VerilatedVcdC	*verilatorWaveformTracer;
#endif
  std::ofstream* logFile;
  int reset_length = 64;
  int stall_limit = 2000;
  int stall_count = 0;
  uint64_t cycle_count = 0;
  uint64_t event_counters[numEvents];
  uint64_t fp_event_counters[fp_numEvents];
  uint64_t LargeTraceSigs_counter[num_LargeTraceSigs]; //count how many are accumulated
  uint64_t max_LargeTraceSigs[num_LargeTraceSigs] = {}; //holds the max sigs recorded
  unsigned long long LargeTraceSigs_accumulate[num_LargeTraceSigs]; //accumulate the sigs

  bool collect_stats = false;
  bool program_complete = false;

  void update_stats();
  void update_UART();
  void update_memory();
  uint32_t instruction_r;
  uint64_t data_out_r;

};
#endif
