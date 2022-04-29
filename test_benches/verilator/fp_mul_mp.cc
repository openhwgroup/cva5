#include <cfenv>    
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <cstdlib>
#include "Vfp_mul_mp_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <random>
#include <limits>

#define TRACE_ON
using namespace std;
typedef unsigned long long int ull;
typedef unsigned int ul;
int i=0;

struct test_case_t {
    ul input1;
    ul input2;
    int rm;
    ul expected_output;
    test_case_t (float input1_, float input2_, int rm_) {
        #pragma STDC FENV_ACCESS ON
        if (rm_ == 1) {
            std::fesetround(FE_TOWARDZERO);
        } else if (rm_ == 0){
            std::fesetround(FE_TONEAREST);
        } else if (rm_ == 3) {
            std::fesetround(FE_UPWARD);
        } else if (rm_ == 2) {
            std::fesetround(FE_DOWNWARD);
        } 
        float result = input1_ * input2_;
        input1 = *(ul*)(&input1_);
        input2 = *(ul*)(&input2_);
        rm = rm_;
        expected_output = *(ul*)(&result);
        cout.precision(15);
        cout << i  << hex << 
        "\trs1: 0x" << *(ul*)(&input1_) << "(" << input1_ << ")" <<
        "\trs2: 0x" << *(ul*)(&input2_) << "(" << input2_ << ")" <<
        "\texpected_output: 0x" << *(ul*)(&expected_output) << "(" << expected_output << ")" << endl;
    
    }
};
queue<test_case_t> test_queue;
queue<ul> expected_output_queue;
float get_float1();

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

int main(int argc, char **argv) {
    cout << "FP Mul Test" <<endl;
    float total_error = 0.0;
    for (i = 0; i < 5; i++) {
        float rs1 = get_float1();
        float rs2 = get_float1();
        test_queue.push(test_case_t(rs1, rs2, 4));
        }

    //test_queue.push(test_case_t(0.000000000000000000000000000000000001, 0.000000000000000000000001, rm)); //different result from c++ implementation; taiga fpu is closer to exact result
    //float test1 = 0.000000000000000000000000000000000001;
    //float test2 = 0.000000000000000000000001;
    //float result = 0;
    //test_queue.push(test_case_t(*(float*)(&test1), *(float*)(&test2), rm));
    //cout.precision(20);
    //std::fesetround(FE_UPWARD);
    //result = test1 * test2;
    //cout << hexfloat;
    //cout << result <<  " upward"  
    //<< defaultfloat << "-> " << (result) << endl;
    //std::fesetround(FE_TOWARDZERO);
    //result = test1 * test2;
    //cout << hexfloat;
    //cout << result <<  " zero"  
    //<< defaultfloat << "-> " << (result) << endl;
    //std::fesetround(FE_DOWNWARD);
    //result = test1 * test2;
    //cout << hexfloat;
    //cout << result <<  " down"  
    //<< defaultfloat << "-> " << (result) << endl;
    //std::fesetround(FE_TONEAREST);
    //result = test1 * test2;
    //cout << hexfloat;
    //cout << result <<  " ner" 
    //<< defaultfloat << "-> " << (result) << endl;    
    // test_queue.push(test_case_t(-5290.74,-5192.57, 1));
    // test_queue.push(test_case_t(1.0, 1.5, FADD, 1));


    // float d = 1.5;
    // cout << hex << *(ul*)(&d) << endl;

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
    Vfp_mul_mp_simulation_wrapper *tb = new Vfp_mul_mp_simulation_wrapper;

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
                    << "\tDelta: " << *(float*)(&expected_output_queue.front()) - *(float*)(&tb->rd) 
                    <<endl;
                    total_error += *(float*)(&expected_output_queue.front()) - *(float*)(&tb->rd);
                } else {
                    cout.precision(20);
                    cout << "Test Passed " << test_count <<endl;;
                    cout << hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(float*)(&expected_output_queue.front()) << ")" 
                    << "\tOutput Received: 0x" << tb->rd << "(" << *(float*)(&tb->rd) << ")"
                    << "\tDelta: " << *(float*)(&expected_output_queue.front()) - *(float*)(&tb->rd) 
                    <<endl;
                } 
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
    cout << dec << total_error << endl;

    #ifdef TRACE_ON
	    tracer->flush();
	    tracer->close();
    #endif

    logFile.close();
    sigFile.close();
    delete tb;
    exit(EXIT_SUCCESS);


}
