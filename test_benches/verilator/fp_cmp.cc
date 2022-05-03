#include "Vfp_cmp_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
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
using namespace std;
typedef unsigned long long int ull;

struct test_case_t {
  ull input1;
  ull input2;
  int rm;
  int expected_output;
  test_case_t(double rs1, double rs2, int rm_, int expected_output_) {
    input1 = *(ull *)(&rs1);
    input2 = *(ull *)(&rs2);
    rm = rm_;
    expected_output = expected_output_;
  }
};
queue<test_case_t> test_queue;
queue<int> expected_output_queue;
double get_double();

double get_double() {
  double min = -10000.0; // std::numeric_limits<double>::min();
  double max = 10000.0;  // std::numeric_limits<double>::max();

  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_real_distribution<double> dis(min, max);
  return dis(gen);
}

std::ifstream cmp_inputs("/localhdd/yuhuig/Research/Tests/subnormal/"
                         "test_benches/verilator/fcmp_tests.txt");

int main(int argc, char **argv) {
  int i = 0;
  std::string line;
  while (i < 22000 && std::getline(cmp_inputs, line)) {
    std::getline(cmp_inputs, line);
    std::getline(cmp_inputs, line);
    std::istringstream iss(line);
    std::vector<std::string> fcmp_input_rs1_rs2;
    int j = 0;
    while (iss && j < 3) {
      string rs;
      if (!std::getline(iss, rs, ','))
        break;
      fcmp_input_rs1_rs2.push_back(rs);
    }
    ull rs1_ull, rs2_ull, rm;
    rs1_ull = std::stoull(fcmp_input_rs1_rs2[0], NULL, 16);
    rs2_ull = std::stoull(fcmp_input_rs1_rs2[1], NULL, 16);
    rm = std::stoull(fcmp_input_rs1_rs2[2], NULL, 16);
    fcmp_input_rs1_rs2.clear();
    //std::cout << std::hex << rs1_ull << " " << rs2_ull << " " << rm << "\n";

    double rs1 = *(ull *)(&rs1_ull);
    double rs2 = *(ull *)(&rs2_ull);
    int rm_ = rm;
    int expected_output;
    if (rm_ == 0) {
      expected_output = (rs1 <= rs2) ? 1 : 0;
    } else if (rm_ == 1) {
      expected_output = (rs1 < rs2) ? 1 : 0;
    } else if (rm_ == 2) {
      expected_output = (rs1 == rs2) ? 1 : 0;
    }
    test_queue.push(test_case_t(rs1, rs2, rm_, expected_output));
    i++;
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
  Vfp_cmp_simulation_wrapper *tb = new Vfp_cmp_simulation_wrapper;

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
      if (test_queue.size() != 0 && tb->ready == 1) {
        tb->new_request = 1;
        tb->rs1 = *(ull *)(&test_queue.front().input1);
        tb->rs2 = *(ull *)(&test_queue.front().input2);
        tb->fn3 = test_queue.front().rm;
        expected_output_queue.push(test_queue.front().expected_output);
        // cout << "pushed in expected_output: " <<
        // test_queue.front().expected_output<<endl;
        test_queue.pop();
      } else {
        tb->new_request = 0;
        tb->rs1 = 0;
        tb->rs2 = 0;
      }

      // Recieve Output
      if (tb->done) {
        cout << "Done";
        if (expected_output_queue.front() != tb->rd) {
          testFailed = true;
          cout << "Test Failed " << test_count << endl;
          ;
          cout << "\tExpected Output: " << expected_output_queue.front()
               << "\tOutput Received: " << tb->rd << endl;
        } else {
          cout << "\tExpected Output: " << expected_output_queue.front()
               << "\tOutput Received: " << tb->rd << endl;
        }
        //cout << endl << endl;
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
