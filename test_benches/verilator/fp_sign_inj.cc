#include "Vfp_sign_inj_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <queue>
#include <random>
#include <sstream>
#include <stdlib.h>
#include <string>

#define TRACE_ON
#define J 0
#define JN 1
#define JX 2
using namespace std;
typedef unsigned long long int ull;

struct test_case_t {
  ull input1;
  ull input2;
  int rm;
  ull expected_output;
  test_case_t(double rs1, double rs2, int rm_, double expected_output_) {
    input1 = *(ull *)(&rs1);
    input2 = *(ull *)(&rs2);
    expected_output = *(ull *)(&expected_output_);
    rm = rm_;
    double result;
    bool rs1_sign = rs1 > 0.0 ? 0 : 1;
    bool rs2_sign = rs2 > 0.0 ? 0 : 1;
  }
};

queue<test_case_t> test_queue;
queue<ull> expected_output_queue;
double get_double();

double get_double() {
  double min = -10000.0; // std::numeric_limits<double>::min();
  double max = 10000.0;  // std::numeric_limits<double>::max();

  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_real_distribution<double> dis(min, max);
  return dis(gen);
}

std::ifstream sign_inj_inputs("/localhdd/yuhuig/Research/Tests/subnormal/"
                              "test_benches/verilator/fsign_inj_tests.txt");

int main(int argc, char **argv) {
  std::string line;
  for (int i = 0; i < 65707; i++) {
    std::getline(sign_inj_inputs, line);
    std::istringstream iss(line);
    std::vector<std::string> sign_inj_inputs_vec;
    for (int j = 0; j < 3; j++) {
      std::string rs;
      std::getline(iss, rs, ',');
      sign_inj_inputs_vec.push_back(rs);
    }
    ull rs1_ull = std::stoull(sign_inj_inputs_vec[0], NULL, 16);
    ull rs2_ull = std::stoull(sign_inj_inputs_vec[1], NULL, 16);
    ull rm_ull = std::stoull(sign_inj_inputs_vec[2], NULL, 16);
    sign_inj_inputs_vec.clear();
    // std::cout << std::hex << "0x" << rs1_ull << "\t0x" << rs2_ull << "\t" <<
    // std::dec << rm_ull << "\n";

    double rs1 = *(double *)(&rs1_ull);
    double rs2 = *(double *)(&rs2_ull);
    int rm = rm_ull;
    double result;
    ull rs1_sign = rs1_ull >> 63;
    ull rs2_sign = rs2_ull >> 63;
    if (rm == 0) {
      result = fabs(rs1) * pow(-1, rs2_sign);
    } else if (rm == 1) {
      result = fabs(rs1) * (-pow(-1, rs2_sign));
    } else if (rm = 2) {
      result = fabs(rs1) * (pow(-1, rs1_sign ^ rs2_sign));
    }
    test_queue.push(test_case_t(rs1, rs2, rm, result));
    std::cout << "rs1: 0x" << std::hex << rs1_ull << "\trs2_sign: " << rs2_sign
              << "\trm:" << std::dec << rm << "\tExpected: 0x" << std::hex << *(ull*)(&result) << "\n";
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
  Vfp_sign_inj_simulation_wrapper *tb = new Vfp_sign_inj_simulation_wrapper;

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
      tb->new_request = 0;
    } else {
      tb->rst = 0;
      if (test_queue.size() == 0) {
        tb->new_request = 0;
      }

      if (test_queue.size() != 0 && tb->ready == 1) {
        tb->new_request = 1;
        tb->rs1 = *(ull *)(&test_queue.front().input1);
        tb->rs2 = *(ull *)(&test_queue.front().input2);
        tb->rm = test_queue.front().rm;
        tb->hidden = isnormal(test_queue.front().input1);
        expected_output_queue.push(test_queue.front().expected_output);
        test_queue.pop();
      } else {
        tb->new_request = 0;
      }

      // Recieve Output
      if (tb->done) {
        cout << "tb->done =" << tb->done << endl;
        if (expected_output_queue.front() != tb->rd) {
          testFailed = true;
          cout << "Test Failed " << test_count << endl;
          ;
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
