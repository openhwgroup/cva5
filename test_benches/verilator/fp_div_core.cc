#include "Vfp_div_core_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <cfenv>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <queue>
#include <random>
#include <stdlib.h>

#define TRACE_ON

using namespace std;
typedef unsigned long long int ull;

struct test_case_t {
  ull input1;
  ull input2;
  int rm;
  ull expected_output;
  test_case_t(double input1_, double input2_, int rm_,
              double expected_output_) {
    double div_result = input1_ / input2_;
    input1 = *(ull *)(&input1_);
    input2 = *(ull *)(&input2_);
    rm = rm_;
    expected_output = *(ull *)(&expected_output_);
  }
};
queue<test_case_t> test_queue;
queue<ull> expected_output_queue;
double get_double1();
double get_double2();

double get_double1() {
  ull min = -20000000000000000; // std::numeric_limits<double>::min();
  ull max = 200000000000000000; // std::numeric_limits<double>::max();

  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<unsigned long long int> dis(min, max);
  ull rand_ull = dis(gen);
  return *(double *)(&rand_ull);
}

double get_double2() {
  double min =
      -2000000000000000000000000000.0; // std::numeric_limits<double>::min();
  double max =
      20000000000000000000000000000.0; // std::numeric_limits<double>::max();

  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_real_distribution<double> dis(min, max);
  return dis(gen);
}

int main(int argc, char **argv) {
  int rm = 3;
#pragma STDC FENV_ACCESS ON
  if (rm == 1) {
    std::fesetround(FE_TOWARDZERO);
  } else if (rm == 0) {
    std::fesetround(FE_TONEAREST);
  } else if (rm == 3) {
    std::fesetround(FE_UPWARD);
  } else if (rm == 2) {
    std::fesetround(FE_DOWNWARD);
  }

  for (int i = 0; i < 1; i++) {
     double rs1 = get_double2();
     double rs2 = get_double2();
    //double rs1 = 9.0;
    //double rs2 = 3.0;
    double expected_output = rs1 / rs2;
    test_queue.push(test_case_t(rs1, rs2, rm, expected_output));
    cout << i << " -- " << hex << "rs1: 0x" << *(ull *)(&rs1) << "(" << rs1
         << ")"
         << "\trs2: 0x" << *(ull *)(&rs2) << "(" << rs2 << ")"
         << "\texpected_output: 0x" << *(ull *)(&expected_output) << "("
         << expected_output << ")" << endl;
  }

  ofstream logFile, sigFile;
  bool logPhase; // Log phase vs signature phase used for compliance tests
  bool stallDetected = false;
  bool testFailed = false;
  int stall_cycles = 0;
  int test_count = 0;

  // Initialize Verilators variables
  Verilated::commandArgs(argc, argv);

#ifdef TRACE_ON
  Verilated::traceEverOn(true);
#endif

  if (!argv[1]) {
    cout << "Missing log file name.\n";
    exit(EXIT_FAILURE);
  }

  if (!argv[2]) {
    cout << "Missing signature file name.\n";
    exit(EXIT_FAILURE);
  }
  logFile.open(argv[1]);
  sigFile.open(argv[2]);

  // Create an instance of our module under test
  Vfp_div_core_simulation_wrapper *tb = new Vfp_div_core_simulation_wrapper;

#ifdef TRACE_ON
  cout << "Tracing" << endl;
  VerilatedVcdC *tracer;
  tracer = new VerilatedVcdC;
  tb->trace(tracer, 99);
  tracer->open("sim_results.vcd");
#endif

  cout << "--------------------------------------------------------------\n"
       << endl;
  cout << "   Starting Simulation, logging to: " << argv[1] << "\n";
  cout << "--------------------------------------------------------------\n"
       << endl;
  int reset_count = 0;
  uint64_t cycle_count = 0;
  tb->rst = 1;
  logPhase = true;

  while (!Verilated::gotFinish()) {
    tb->clk = 1;
    tb->eval();

    /********************************TEST BENCH
     * START****************************************/

    if (reset_count <= 10) {
      reset_count++;
      tb->start = 0;
    } else {
      // cout << dec << "Cycle: " << cycle_count <<
      //"\ttb->start :" << tb->start <<
      //"\ttb->done =" << tb->done << endl;
      tb->rst = 0;
      if (test_queue.size() > 0) {
        // if (cycle_count == 0 && tb->start == 0){
        //     tb->start = 1;
        // } else {
        //     tb->start = 0;
        // }
        tb->start = 1 && (cycle_count == 11);

        tb->rs1 = *(ull *)(&test_queue.front().input1);
        tb->rs2 = *(ull *)(&test_queue.front().input2);
        tb->rm = test_queue.front().rm;
        expected_output_queue.push(test_queue.front().expected_output);
        test_queue.pop();
      } else {
        tb->start = 0;
        tb->rs1 = tb->rs1;
        tb->rs2 = tb->rs2;
        tb->rm = tb->rm;
      }

      // Recieve Output
      if (tb->done) {
        tb->ack = 1;
        cout << "finished in " << dec << cycle_count - 11 << " cycles" << endl;
        cout.precision(20);
        if (expected_output_queue.front() != tb->rd) {
          testFailed = true;
          cout << "Test Failed " << test_count << "\t";
          cout << hex << "Expected Output: 0x" << expected_output_queue.front()
               << "(" << *(double *)(&expected_output_queue.front()) << ")"
               << "\tOutput Received: 0x" << tb->rd << "("
               << *(double *)(&tb->rd) << ")" << endl;
        } else {
          cout << "Test Passed " << test_count << "\t";
          cout << hex << "Expected Output: 0x" << expected_output_queue.front()
               << "(" << *(double *)(&expected_output_queue.front()) << ")"
               << "\tOutput Received: 0x" << tb->rd << "("
               << *(double *)(&tb->rd) << ")" << endl;
        }
        cout << endl << endl;
        expected_output_queue.pop();
        if (expected_output_queue.size() == 0 && test_queue.size() == 0 &&
            stall_cycles > 4) {
          break;
        } else {
          stall_cycles++;
        }
        test_count++;
      }
    }

    /********************************TEST BENCH
     * END****************************************/
    tb->clk = 0;
    tb->eval();

#ifdef TRACE_ON
    tracer->dump(vluint32_t(cycle_count));
#endif
    cycle_count++;
  }

  if (testFailed) {
    cout << "Testbench Failed" << endl << endl;
  } else {
    cout << "Testbench Passed" << endl << endl;
  }

#ifdef TRACE_ON
  tracer->flush();
  tracer->close();
#endif

  logFile.close();
  sigFile.close();
  delete tb;
  exit(EXIT_SUCCESS);
}
