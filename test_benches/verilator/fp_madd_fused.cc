// TODO: rounding for FADD broken except rounding to zero
// TODO: rounding for FMUl seems ok
// TODO: FMADD is broken cuz FADD? -> check FADD
#include "/localhdd/yuhuig/tools/tabulate/single_include/tabulate/tabulate.hpp"
#include "Vfp_madd_fused_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <algorithm>
#include <cfenv>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <ios>
#include <iostream>
#include <iterator>
#include <limits>
#include <numeric>
#include <ostream>
#include <queue>
#include <random>
#include <sstream>
#include <stdlib.h>
#include <string>
#include <vector>
using namespace tabulate;
vluint64_t main_time = 0; // Current simulation time
// This is a 64-bit integer to reduce wrap over issues and
// allow modulus.  This is in units of the timeprecision
// used in Verilog (or from --timescale-override)

double sc_time_stamp() { // Called by $time in Verilog
  return main_time;      // converts to double, to match
                         // what SystemC does
}

#pragma STDC FENV_ACCESS ON
#define TRACE_ON
#define FMADD 67
#define FMSUB 71
#define FNMSUB 75
#define FNMADD 79
using namespace std;
typedef unsigned long long int ull;
std::vector<int> FMA_opcode = {FMADD, FMSUB, FNMSUB, FNMADD};
std::vector<int> FMA_instruction = {4, 2, 1};
std::vector<int> fadd_fn7 = {0b0000001, 0b0000101};

union FP {
  uint64_t fp_hex;
  double fp;
};

struct test_case_t {
  ull input1;
  ull input2;
  ull input3;
  int rm;
  int op;
  int id;
  int instruction;
  int fn7;
  // ull expected_output;
  long double expected_output;
  string operation;
  test_case_t(double input1_, double input2_, double input3_, int fn7_, int op_,
              int id_, int rm_, int instruction_, long double expected_output_,
              const std::string &operation_) {
    input1 = *(ull *)(&input1_);
    input2 = *(ull *)(&input2_);
    input3 = *(ull *)(&input3_);
    rm = rm_;
    op = op_;
    fn7 = fn7_;
    id = id_;
    instruction = instruction_;
    expected_output = expected_output_; //*(ull*)(&expected_output_);
    operation = operation_;
  }
};
queue<test_case_t> test_queue;
queue<long double> expected_output_queue_fmul;
queue<long double> expected_output_queue_fadd;
queue<long double> expected_output_queue_fmadd;
std::vector<long double> dut_stdev;
std::vector<std::vector<double>> dut_results;
std::vector<long double> dut_rounding_error_avg;
std::vector<long double> expected_output;
std::vector<double> dut_mean;
double rand_normal_dp();
double rand_subnormal_dp();

long double stdev(std::vector<double> vec, long double &mean);

double rand_normal_dp() {
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<unsigned long> dis(
      std::numeric_limits<unsigned long>::min(),
      std::numeric_limits<unsigned long>::max());
  FP fp;
  fp.fp_hex = dis(gen);
  fp.fp_hex = fp.fp_hex & 0xffefffffffffffff;
  return (fp.fp);
}

std::vector<std::string> split(std::string s) {
  std::vector<std::string> vec;
  int pos = 0;
  while (std::string::npos != (pos = s.find(',', pos))) {
    vec.push_back(s.substr(0, pos));
    s = s.substr(pos + 1);
  }
  vec.push_back(s);
  return vec;
}

double rand_subnormal_dp() {
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<> dis(std::numeric_limits<int>::min(),
                                      std::numeric_limits<int>::max());
  FP fp;
  fp.fp_hex = dis(gen);
  fp.fp_hex =
      fp.fp_hex & 0x000fffffffffffff; // 0 out the sign and exponent bits
  return (fp.fp);
}

long double stdev(std::vector<double> vec, long double &mean) {
  long double sum = std::accumulate(vec.begin(), vec.end(), 0.0);
  mean = sum / vec.size();

  std::vector<long double> diff(vec.size());
  std::transform(vec.begin(), vec.end(), diff.begin(),
                 std::bind2nd(std::minus<long double>(), mean));
  long double sq_sum =
      std::inner_product(diff.begin(), diff.end(), diff.begin(), 0.0);
  long double stdev = std::sqrt(sq_sum / vec.size());
  // std::cout << "sum:" << sum << "\n";
  // std::cout << "mean:" << mean << "\ndiff vector:";
  // std::for_each (diff.begin(), diff.end(), [](long double a){std::cout<<a<<"
  // ";});std::cout << "\n"; std::cout << "sq_sum:" << sq_sum << "\n"; std::cout
  // << "sample size:" << vec.size() << "\n";
  return stdev;
}

std::ifstream fmul_inputs("/localhdd/yuhuig/Research/Tests/compliance-level-data-collection/subnormal-master/"
                          "test_benches/verilator/fma_tests.txt");

int main(int argc, char **argv) {
  int test_number = 10;
  int mca_iteration_max = 1;
  std::vector<std::vector<long double>> rounding_error;
  rounding_error.push_back(std::vector<long double>());
  dut_results.push_back(std::vector<double>());
  int test_failed = 0;
  double total_error = 0.0;
  int rm = 0;
  std::ostringstream streamObj;
  std::ostringstream rs1Obj;
  std::ostringstream rs2Obj;
  std::ostringstream rs3Obj;
  std::ostringstream opObj;
  std::ostringstream testnumObj;
  std::ostringstream expectedObj;
  Table universal_constants;
  Table inputs;
  inputs.add_row({"test num", "op", "rs1", "rs2", "rs3", "expected"});

  if (rm == 1) {
    std::fesetround(FE_TOWARDZERO);
  } else if (rm == 0) {
    std::fesetround(FE_TONEAREST);
  } else if (rm == 3) {
    std::fesetround(FE_UPWARD);
  } else if (rm == 2) {
    std::fesetround(FE_DOWNWARD);
  }

  // for (int i = 0; i < test_number; i++) {
  std::string line;
  int i;
  while (std::getline(fmul_inputs, line) && (i < test_number)) {
    long double result = 0.0;
    int op = FMSUB;
    int instruction = FMA_instruction[2]; //[rand()%3];
    int fn7 = fadd_fn7[1];
    string operation;

    std::istringstream iss(line);
    int j = 0;
    std::vector<std::string> fmul_input_rs1_rs2;
    //std::cout << line << "\n";
    while (iss && j < 3) {
      string rs;
      if (!getline(iss, rs, ',')) {
        break;
      }
      fmul_input_rs1_rs2.push_back(rs);
    }
    ull sub1, sub2, sub3;
    sub1 = std::stoull(fmul_input_rs1_rs2[0], NULL, 16);
    sub2 = std::stoull(fmul_input_rs1_rs2[1], NULL, 16);
    sub3 = std::stoull(fmul_input_rs1_rs2[2], NULL, 16);
    fmul_input_rs1_rs2.clear();
     //std::cout << std::hex << sub1 << " " << sub2 << " " << sub3 << "\n";
    double rs1_L = *(double *)(&sub1);
    double rs2_L = *(double *)(&sub2);
    double rs3_L = *(double *)(&sub3);
    double rs1 = rs1_L;
    double rs2 = rs2_L;
    double rs3 = rs3_L;
    if (instruction == 4) {
      // handle fma instruction
      if (op == FMADD) {
        result = rs1_L * rs2_L + rs3_L;
        operation = "FMADD";
      } else if (op == FMSUB) {
        result = rs1_L * rs2_L - rs3_L;
        operation = "FMSUB";
      } else if (op == FNMSUB) {
        result = -(rs1_L * rs2_L) + rs3_L;
        operation = "FNMSUB";
      } else if (op == FNMADD) {
        result = -(rs1_L * rs2_L) - rs3_L;
        operation = "FNMADD";
      }
    } else if (instruction == 2) {
      // handle fadd
      if (fn7 == 0b0000001) {
        result = rs1_L + rs2_L;
        operation = "FADD";
      } else if (fn7 == 0b0000101) {
        result = rs1_L - rs2_L;
        operation = "FSUB";
      }
    } else if (instruction == 1) {
      // handle fmul
      result = rs1_L * rs2_L;
      operation = "FMUL";
    }
    for (int ite = 0; ite < mca_iteration_max; ite++) {
      test_queue.push(test_case_t(rs1, rs2, rs3, fn7, op, i, rm, instruction,
                                  result, operation));
    }

    testnumObj.str(std::string());
    testnumObj.clear();
    testnumObj << i;

    double result_double = result;
    opObj.str(std::string());
    opObj.clear();
    opObj << operation;

    rs1Obj.str(std::string());
    rs1Obj.clear();
    rs1Obj << std::scientific << std::setprecision(15) << rs1 << "\n"
           << "0x" << std::setfill('0') << std::setw(16) << std::hex
           << *(ull *)(&rs1);

    rs2Obj.str(std::string());
    rs2Obj.clear();
    rs2Obj << std::scientific << std::setprecision(15) << rs2 << "\n"
           << "0x" << std::setfill('0') << std::setw(16) << std::hex
           << *(ull *)(&rs2);

    rs3Obj.str(std::string());
    rs3Obj.clear();
    rs3Obj << std::scientific << std::setprecision(15) << rs3 << "\n"
           << "0x" << std::setfill('0') << std::setw(16) << std::hex
           << *(ull *)(&rs3);

    expectedObj.str(std::string());
    expectedObj.clear();
    expectedObj << std::scientific << result << "\n"
                << "0x" << std::setfill('0') << std::setw(16) << std::hex
                << *(ull *)(&result_double);

    inputs.add_row({testnumObj.str(), opObj.str(), rs1Obj.str(), rs2Obj.str(),
                    rs3Obj.str(), expectedObj.str()});
    i++;
  }
  std::cout << inputs << std::endl;

  ofstream logFile, sigFile;
  bool logPhase; // Log phase vs signature phase used for compliance tests

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
  Vfp_madd_fused_simulation_wrapper *tb = new Vfp_madd_fused_simulation_wrapper;

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
  int mca_madd_count = 0;
  int mca_add_count = 0;
  int mca_mul_count = 0;
  int test_count = 0;
  long double mean;
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
        tb->rs3 = *(ull *)(&test_queue.front().input3);
        tb->op = test_queue.front().op;
        tb->id = test_queue.front().id;
        tb->input_counter = test_queue.front().id;
        tb->rm = test_queue.front().rm;
        tb->instruction = test_queue.front().instruction;
        tb->fn7 = test_queue.front().fn7;
        if (test_queue.front().instruction == 1) {
          // push into mul result queue
          expected_output_queue_fmul.push(test_queue.front().expected_output);
        } else if (test_queue.front().instruction == 2) {
          // push into fadd result queue
          expected_output_queue_fadd.push(test_queue.front().expected_output);
        } else if (test_queue.front().instruction == 4) {
          // push into fmadd result queue
          expected_output_queue_fmadd.push(test_queue.front().expected_output);
        }
        test_queue.pop();
      } else {
        tb->new_request = 0;
        tb->rs1 = 0;
        tb->rs2 = 0;
      }

      // Recieve Output
      if (tb->mul_done) {
        mca_mul_count++;
        tb->mul_ack = 1;
        ull result = tb->mul_rd;
        double result_double = *(double *)(&result);
        double expected_result = expected_output_queue_fmul.front();
        double error = expected_result - result_double;
        dut_results[test_count].push_back(result_double);
        rounding_error[test_count].push_back(error);
        // std::cout.precision(30);
        // std::cout << "Expected: " << expected_result
        //<< "\tDUT returned: " << result_double << "\tError: " << error
        //<< std::endl;
        expected_output_queue_fmul.pop();
        if (mca_mul_count >= mca_iteration_max) {
          long double std_deviation = stdev(dut_results[test_count], mean);
          dut_stdev.push_back(std_deviation);
          expected_output.push_back(expected_result);
          dut_mean.push_back(mean);
          dut_rounding_error_avg.push_back(
              std::accumulate(
                  rounding_error[test_count].begin(),
                  rounding_error[test_count].end(), 0.0,
                  [](double a, double b) { return abs(a) + abs(b); }) /
              rounding_error[test_count].size());
          mca_mul_count = 0;
          test_count++;
          rounding_error.push_back(std::vector<long double>());
          dut_results.push_back(std::vector<double>());
        }
      }

      if (tb->madd_done) {
        mca_madd_count++;
        tb->madd_ack = 1;
        ull result = tb->madd_rd;
        double result_double = *(double *)(&result);
        double expected_result = expected_output_queue_fmadd.front();
        double error = expected_result - result_double;
        dut_results[test_count].push_back(result_double);
        rounding_error[test_count].push_back(error);
        // std::cout.precision(30);
        // std::cout << "Expected: " << expected_result
        //<< "\tDUT returned: " << result_double << "\tError: " << error
        //<< std::endl;
        expected_output_queue_fmadd.pop();
        if (mca_madd_count >= mca_iteration_max) {
          long double std_deviation = stdev(dut_results[test_count], mean);
          dut_stdev.push_back(std_deviation);
          expected_output.push_back(expected_result);
          dut_mean.push_back(mean);
          dut_rounding_error_avg.push_back(
              std::accumulate(
                  rounding_error[test_count].begin(),
                  rounding_error[test_count].end(), 0.0,
                  [](double a, double b) { return abs(a) + abs(b); }) /
              rounding_error[test_count].size());
          mca_madd_count = 0;
          test_count++;
          rounding_error.push_back(std::vector<long double>());
          dut_results.push_back(std::vector<double>());
        }
      }

      if (tb->add_done) {
        mca_add_count++;
        tb->madd_ack = 1;
        ull result = tb->madd_rd;
        double result_double = *(double *)(&result);
        double expected_result = expected_output_queue_fadd.front();
        double error = expected_result - result_double;
        dut_results[test_count].push_back(result_double);
        rounding_error[test_count].push_back(error);
        // std::cout.precision(30);
        // std::cout << "Expected: " << expected_result
        //<< "\tDUT returned: " << result_double << "\tError: " << error
        //<< std::endl;
        expected_output_queue_fadd.pop();
        if (mca_add_count >= mca_iteration_max) {
          long double std_deviation = stdev(dut_results[test_count], mean);
          dut_stdev.push_back(std_deviation);
          expected_output.push_back(expected_result);
          dut_mean.push_back(mean);
          dut_rounding_error_avg.push_back(
              std::accumulate(
                  rounding_error[test_count].begin(),
                  rounding_error[test_count].end(), 0.0,
                  [](double a, double b) { return abs(a) + abs(b); }) /
              rounding_error[test_count].size());
          mca_add_count = 0;
          test_count++;
          rounding_error.push_back(std::vector<long double>());
          dut_results.push_back(std::vector<double>());
        }
      }

      if (expected_output_queue_fadd.size() == 0 &&
          expected_output_queue_fmadd.size() == 0 &&
          expected_output_queue_fmul.size() == 0 && test_queue.size() == 0)
        break;
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

  universal_constants.add_row(
      {"test num", "expected", "mean", "avg rounding error", "stdev", "std err",
       "(std err precision)", "rel err", "(rel err precision"});
  std::vector<double> data(9);
  std::vector<std::string> data_string;
  std::vector<std::string> test;
  for (int i = 0; i < test_number; i++) {
    data[0] = i;
    data[1] = expected_output.at(i);
    data[2] = dut_mean.at(i);
    data[3] = dut_rounding_error_avg.at(i);
    data[4] = dut_stdev.at(i);
    data[5] = dut_stdev.at(i) / sqrt(mca_iteration_max);
    data[6] = int(-log10(abs(
        (dut_stdev.at(i) / sqrt(mca_iteration_max) / expected_output.at(i)))));
    data[7] = abs(expected_output.at(i) - dut_mean.at(i)) /
              abs(expected_output.at(i));
    data[8] = int(-log10(abs(expected_output.at(i) - dut_mean.at(i)) /
                         abs(expected_output.at(i))));
    // std::transform(std::begin(data), std::end(data),
    // data_string.begin(), // std::back_inserter(data),
    //[](auto d) { return std::to_string(d); });
    streamObj.str(std::string());
    streamObj.clear();
    streamObj << std::dec << std::fixed << std::setprecision(0) << data[0];
    data_string.push_back(streamObj.str());

    streamObj.str(std::string());
    streamObj.clear();
    // streamObj << std::scientific << data[1];
    double tmp_double = data[1];
    ull tmp = *(ull *)(&tmp_double);
    streamObj << std::hex << "0x" << std::setw(16) << std::setfill('0') << tmp;
    data_string.push_back(streamObj.str());

    streamObj.str(std::string());
    streamObj.clear();
    // streamObj << std::scientific << data[2];
    tmp_double = data[2];
    tmp = *(ull *)(&tmp_double);
    streamObj << std::hex << "0x" << std::setw(16) << std::setfill('0') << tmp;
    data_string.push_back(streamObj.str());

    streamObj.str(std::string());
    streamObj.clear();
    streamObj << std::scientific << data[3];
    data_string.push_back(streamObj.str());

    streamObj.str(std::string());
    streamObj.clear();
    streamObj << std::scientific << data[4];
    data_string.push_back(streamObj.str());

    streamObj.str(std::string());
    streamObj.clear();
    streamObj << std::scientific << data[5];
    data_string.push_back(streamObj.str());

    streamObj.str(std::string());
    streamObj.clear();
    streamObj << std::scientific << data[6];
    data_string.push_back(streamObj.str());

    streamObj.str(std::string());
    streamObj.clear();
    streamObj << std::scientific << data[7];
    data_string.push_back(streamObj.str());

    streamObj.str(std::string());
    streamObj.clear();
    streamObj << std::scientific << data[8];
    data_string.push_back(streamObj.str());

    std::vector<variant<std::string, const char *, tabulate::Table>> mapped;
    for (const auto &it : data_string) {
      const auto varRow =
          variant<std::string, const char *, tabulate::Table>(it);
      mapped.push_back(varRow);
    }

    universal_constants.add_row(mapped);
    mapped.clear();
    data_string.clear();
  }
  universal_constants.column(0).format().font_align(FontAlign::center);
  universal_constants.column(1).format().font_align(FontAlign::left);
  std::cout << universal_constants << std::endl;

#ifdef TRACE_ON
  tracer->flush();
  tracer->close();
#endif

  logFile.close();
  sigFile.close();
  delete tb;
  exit(EXIT_SUCCESS);
}
