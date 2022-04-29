#include <cfenv>
#include <cmath>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <cstdlib>
#include "Vfp_add_mp_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <random>
#include <limits>

#define TRACE_ON
#define FADD 0b0000001
#define FSUB 0b0000101
using namespace std;
typedef unsigned long long int ull;
typedef unsigned int ul;

struct test_case_t {
    ul input1;
    ul input2;
    int fn7;
    int rm;
    ul expected_output;
    test_case_t (float input1_, float input2_, int fn7_, int rm_) {
        float addition = input1_ + input2_;
        float subtraction = input1_ - input2_;
        input1 = *(ul*)(&input1_);
        input2 = *(ul*)(&input2_);
        fn7 = fn7_;
        rm = rm_;
        if (fn7_ == FADD)
            expected_output = *(ul*)(&addition);
        else 
            expected_output = *(ul*)(&subtraction);
    }
};
queue<test_case_t> test_queue;
queue<ul> expected_output_queue;
float get_float1();
float get_float2();

float get_float1(){
    ul min = std::numeric_limits<unsigned int>::min();
    ul max = std::numeric_limits<unsigned int>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    //std::uniform_real_distribution<float> dis(min,max);
    std::uniform_int_distribution<ul> dis(min, max);
    ul rand_ul = dis(gen);
    return *(float*)(&rand_ul);
}

float get_float2(){
    float min = -10000000000000000000000000000.0;//std::numeric_limits<float>::min();
    float max = 242000000000000000000000000000.0;//std::numeric_limits<float>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<float> dis(min,max);
    return dis(gen);
}

int main(int argc, char **argv) {
    cout << "FP ADD Test" << endl;
    #pragma STDC FENV_ACCESS ON
    float total_error = 0.0;
    float delta = 0.0;
    int rm = 0;
    std::string op;
    float expected_output = 0;
    if (rm == 1) {
        std::fesetround(FE_TOWARDZERO);
    } else if (rm == 0){
        std::fesetround(FE_TONEAREST);
    } else if (rm == 3) {
        std::fesetround(FE_UPWARD);
    } else if (rm == 2) {
        std::fesetround(FE_DOWNWARD);
    }
    for (int i = 0; i < 10; i++) {
        float rs1 = get_float1();
        float rs2 = get_float1();
        if (i%2 == 1) {
            test_queue.push(test_case_t(rs1, rs2, FSUB, rm));
            op = "SUB";
            expected_output = rs1 - rs2;
        }
        else {
            test_queue.push(test_case_t(rs1, rs2, FADD, rm));
            op = "ADD";
            expected_output = rs1 + rs2;
        }
        cout.precision(20);
        cout << i << " --" << op << hex << " rs1: 0x" << *(ul*)(&rs1) << "(" << rs1 << ")" <<
        "\trs2: 0x" << *(ul*)(&rs2) << "(" << rs2 << ")" <<
        "\texpected_output: 0x" << *(ul*)(&expected_output) << "(" << expected_output << ")" << endl;
    }
    test_queue.push(test_case_t(0.0,0.0,FADD,1));
    ofstream logFile, sigFile;
    bool logPhase; //Log phase vs signature phase used for compliance tests
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
    logFile.open (argv[1]);
    sigFile.open (argv[2]);

    // Create an instance of our module under test
    Vfp_add_mp_simulation_wrapper *tb = new Vfp_add_mp_simulation_wrapper;

   #ifdef TRACE_ON
     cout << "Tracing" << endl;
      VerilatedVcdC	*tracer;
	   tracer = new VerilatedVcdC;
	   tb->trace(tracer, 99);
	   tracer->open("sim_results.vcd");
   #endif

    cout << "--------------------------------------------------------------\n" << endl;
    cout << "   Starting Simulation, logging to: " << argv[1] << "\n";
    cout << "--------------------------------------------------------------\n" << endl;
    int reset_count = 0;
    uint64_t cycle_count = 0;
    tb->rst = 1;
    logPhase = true;

    while(!Verilated::gotFinish()) {
	    tb->clk = 1;
	    tb->eval();

/********************************TEST BENCH START****************************************/
       
        if (reset_count <= 10) {
            reset_count ++;
            tb->new_request = 0;
        } 
        else {
            tb->rst = 0;
            if (test_queue.size() == 0) {
                tb->new_request = 0;
            }

            if (test_queue.size() != 0 && tb->ready == 1){
                tb->new_request = 1;
                tb->rs1 =  *(ul*)(&test_queue.front().input1);
                tb->rs2 =  *(ul*)(&test_queue.front().input2);
                tb->fn7 =  test_queue.front().fn7;
                tb->rm = test_queue.front().rm;
                expected_output_queue.push(test_queue.front().expected_output);
                test_queue.pop();
            }
            else {
                tb->new_request = 0;
                tb->rs1 = 0;
                tb->rs2 = 0;
            }

            //Recieve Output
            if(tb->done){
                //cout << "tb->done =" << tb->done << endl;
                if (expected_output_queue.front() != tb->rd){
                    testFailed = true;
                    cout.precision(20);
                    cout << "Test Failed " << test_count <<endl;;
                    cout << hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(float*)(&expected_output_queue.front()) << ")" 
                    << "\tOutput Received: 0x" << tb->rd << "(" << *(float*)(&tb->rd) << ")"
                    <<endl;
                    total_error += abs(*(float*)(&tb->rd) -  *(float*)(&expected_output_queue.front()));
                }// else {
                    //cout.precision(20);
                    //cout << test_count << ": " << 
                            //hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(float*)(&expected_output_queue.front()) << ")" 
                    //<< "\tOutput Received: 0x" << tb->rd << "(" << *(float*)(&tb->rd) << ")"
                    //<<endl;

                //}
                cout << endl << endl;
                expected_output_queue.pop();
                if (expected_output_queue.size() == 0 && test_queue.size() == 0 && stall_cycles > 4){
                    break;
                } else {
                    stall_cycles++;
                }
                test_count++;
            }
        }
        
/********************************TEST BENCH END****************************************/
	    tb->clk = 0;
	    tb->eval();

		#ifdef TRACE_ON
		    tracer->dump(vluint32_t(cycle_count));
		#endif
        cycle_count++;
    }

    if(testFailed) {
        cout << "Testbench Failed"<< endl << endl;
    }
    else{
        cout << "Testbench Passed" << endl << endl;
    }
    cout << dec << total_error <<endl;

    #ifdef TRACE_ON
	    tracer->flush();
	    tracer->close();
    #endif

    logFile.close();
    sigFile.close();
    delete tb;
    exit(EXIT_SUCCESS);


}
