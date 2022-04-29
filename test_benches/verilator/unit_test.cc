#include "unit_test.h"
#include <iostream>
#include <math.h>
#include <ostream>
#include <sstream>
#include <stdlib.h>
#include <string>
#include <type_traits>

/////////////////////////////////////////////////////////////
// xorshift random number generator
uint64_t rol64(uint64_t x, int k);
uint64_t rol64(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }

struct xoshiro256ss_state {
  uint64_t s[4];
};

template <class TB, typename INT, typename FLOAT>
INT unit_test<TB, INT, FLOAT>::xoshiro256ss(struct xoshiro256ss_state *state) {
  uint64_t *s = state->s;
  uint64_t const result = rol64(s[1] * 5, 7) * 9;
  uint64_t const t = s[1] << 17;
  s[2] ^= s[0];
  s[3] ^= s[1];
  s[1] ^= s[2];
  s[0] ^= s[3];
  s[2] ^= t;
  s[3] = rol64(s[3], 45);
  return result;
}

//////////////////////////////////////////////////////////
// unit test class
template <class TB, typename INT, typename FLOAT>
unit_test<TB, INT, FLOAT>::unit_test(const char *input_file, int _input_count,
                                     const char *output_file) {
  tb = new TB;
  reset_length = 10;
  cycle_count = 0;
  input_count = _input_count;
  verify_count = 0;
  ready = false;
#ifdef TRACE_ON
  accu_error = 0.0;
  Verilated::traceEverOn(true);
#endif

  this->inputs = input_file;
  this->outputs = output_file;
  // std::cout << this->inputs << std::endl;
  tb->clk = 0;
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::start_tracer(const char *tracer_file) {
#ifdef TRACE_ON
  tracer = new VerilatedVcdC;
  tb->trace(tracer, 99);
  tracer->open(tracer_file);
#endif
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::read_inputs() {
  FILE *input_file;
  input_file = fopen(inputs, "r");
  if (input_file == NULL) {
    std::cout << "Error: cannot open file" << *inputs << std::endl;
    exit(-1);
  }
  char line[100];
  char *token;
  char delimit[] = " \n";
  INT tokenBuff[10];
  INT tokenVal;
  while (fgets(line, sizeof(line), input_file) != NULL) {
    input_count++;
    int i = -1;
    token = std::strtok(line, delimit);
    while (token != NULL) {
      tokenVal = std::strtoull(token, NULL, 16);
      i++;
      tokenBuff[i] = tokenVal;
      token = std::strtok(NULL, delimit);
    }
    // std::cout << std::hex << "token0: " << tokenBuff[0] << "\ttoken1: " <<
    // tokenBuff[1] << std::endl;
    test_queue.push(test_case_t(tokenBuff[0], tokenBuff[1]));
    expected_output_queue.push(div(tokenBuff[0], tokenBuff[1]));
  }
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::reset() {
  tb->clk = 0;
  tb->rst = 1;
  for (int i = 0; i < reset_length; i++) {
    tick();
  }
  tb->rst = 0;
  ready = true;
  verify_count = 0;
  std::cout << "DONE reset \n" << std::flush;
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::tick() {
  cycle_count++;
  tb->clk = 1;
  tb->eval();
#ifdef TRACE_ON
  tracer->dump(vluint32_t(10 * cycle_count - 2));
#endif
  cycle_count++;
  this->instruction_cycle++;

  tb->clk = 0;
  tb->eval();
#ifdef TRACE_ON
  tracer->dump(vluint32_t(10 * cycle_count - 2));
#endif

  tb->clk = 1;
  tb->eval();

  drive_inputs();
  verify();
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::drive_inputs() {
  if (!tb->rst && !test_queue.empty() && tb->ready) {
    this->instruction_cycle = 0;
    tb->new_request = 1;
    tb->possible_issue = 1;
    tb->rs1 = test_queue.front().rs1;
    tb->rs2 = test_queue.front().rs2;
    tb->rm = 0; // test_queue.front().rm;
    tb->instruction_id = test_queue.front().id;
#if DIV_SQRT_UNIT == 1
    tb->fn7 = IS_DIV ? 0x0 : 0x20; // 6'b000000 : 6'b100000
#endif
    debug_queue.push(test_queue.front());
    test_queue.pop();
    ready = false;
  } else {
    tb->new_request = 0;
    tb->possible_issue = 0;
    tb->rs1 = 0;
    tb->rs2 = 0;
    tb->rm = 0;
  }
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::verify() {
  if (tb->done) {
    verify_count++;
    tb->ack = 1;
    INT DUT_output = tb->rd;
    INT expected_output = expected_output_queue.front();
    INT rs1 = debug_queue.front().rs1;
    INT rs2 = debug_queue.front().rs2;
    std::setprecision(64);
    if (DUT_output != expected_output) {
      std::cout << std::dec << "Test " << verify_count << " failed\t"
                << std::hex << "Input 0x" << std::setw(16) << std::setfill('0')
                << rs1 << "\t0x" << std::setw(16) << std::setfill('0') << rs2
                << "\nexpected: 0x" << std::setw(16) << std::setfill('0')
                << expected_output << "\treceived: 0x" << std::setw(16)
                << std::setfill('0') << DUT_output << std::endl;
      accu_error +=
          fabs((*(FLOAT *)(&expected_output)) - (*(FLOAT *)(&tb->rd)));
      wrong_result_queue.push(test_case_t(rs1, rs2));
    } else {
      std::cout << std::dec << "\nTest " << verify_count << " passed"
                << std::endl;
    }
    std::cout << std::dec << "Instruction Cycle: " << this->instruction_cycle
              << std::endl;
    std::cout << "\n";
    expected_output_queue.pop();
    tb->ack = 0;
    debug_queue.pop();
    ready = true;
  }
}

template <class TB, typename INT, typename FLOAT>
bool unit_test<TB, INT, FLOAT>::terminate() {
  // extra tick to dump remaining trace signals
  tick();
  return (verify_count >= input_count);
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::print_inputs() {
  while (!expected_output_queue.empty()) {
    std::cout << std::hex << expected_output_queue.front() << std::endl;
    expected_output_queue.pop();
  }
}

template <class TB, typename INT, typename FLOAT>
INT unit_test<TB, INT, FLOAT>::div(INT rs1, INT rs2) {
  FLOAT rs1_float = *(FLOAT *)(&rs1);
  FLOAT rs2_float = *(FLOAT *)(&rs2);
  FLOAT result = rs1_float / rs2_float;
  std::cout << std::hex << std::setw(16) << std::setfill('0') << rs1 << " ("
            << rs1_float << ")\t" << std::setw(16) << std::setfill('0') << rs2
            << "(" << rs2_float << ")"
            << "\tresult :0x" << std::setw(16) << std::setfill('0')
            << (*(INT *)(&result)) << "(" << result << ")" << std::endl;
  return (*(INT *)(&result));
}

template <class TB, typename INT, typename FLOAT>
INT unit_test<TB, INT, FLOAT>::sqrt_custom(FLOAT rs1) {
  std::cout << std::hex << "0x" << *(INT *)(&rs1) << std::endl;
  FLOAT rs1_sqrt = sqrt(rs1);
  INT result_hex = *(INT *)(&rs1_sqrt);
  return result_hex;
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::GenInputs() {
  // new instance of xoshiro256ss_state
  struct xoshiro256ss_state *state = new struct xoshiro256ss_state;

  // get random seed from quantumrandom
  std::ifstream seed_input(this->inputs, std::ios_base::in);
  std::string line;
  const char *cline;
  for (int i = 0; i < 4; i++) {
    std::getline(seed_input, line);
    cline = &line[0];
    this->seed[i] = std::strtoull(cline, NULL, 16);
    state->s[i] = *(uint64_t *)(&this->seed[i]);
  }

  // generate inputs
  for (int i = 0; i < input_count; i++) {
    FLOAT rs1_d = xoshiro256ss(state);
    FLOAT rs2_d = xoshiro256ss(state);
    INT rs1 = *(INT *)(&rs1_d);
    INT rs2 = *(INT *)(&rs2_d);
    test_queue.push(test_case_t(rs1, rs2));
#if DIV_SQRT_UNIT == 1
#if IS_DIV == 1
    expected_output_queue.push(div(rs1, rs2));
#elif IS_DIV == 0
    expected_output_queue.push(sqrt_custom(*(FLOAT *)(&rs1)));
#endif
#endif
  }
}

template <class TB, typename INT, typename FLOAT>
void unit_test<TB, INT, FLOAT>::faulty_output_log() {
  std::ofstream log(this->outputs, std::ios_base::out);
  log << "Logging input pairs with faulty results from Taiga FPU" << std::endl;
  while (!wrong_result_queue.empty()) {
    INT rs1 = wrong_result_queue.front().rs1;
    INT rs2 = wrong_result_queue.front().rs2;
    log << std::hex << "0x" << rs1 << " 0x" << rs2 << std::endl;
    wrong_result_queue.pop();
  }
}

template <class TB, typename INT, typename FLOAT>
unit_test<TB, INT, FLOAT>::~unit_test() {
  faulty_output_log();
  std::cout << "Acccumulated Error: " << accu_error << std::endl;
#ifdef TRACE_ON
  tracer->flush();
  tracer->close();
#endif
  delete tb;
}
