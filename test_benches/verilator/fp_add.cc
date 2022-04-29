#include <cfenv>
#include <cmath>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <cstdlib>
#include "Vfp_add_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <random>
#include <limits>

#define TRACE_ON
#define FADD 0b0000001
#define FSUB 0b0000101
using namespace std;
typedef unsigned long long int ull;

struct test_case_t {
    ull input1;
    ull input2;
    int fn7;
    int rm;
    ull expected_output;
    test_case_t (double input1_, double input2_, int fn7_, int rm_) {
        double addition = input1_ + input2_;
        double subtraction = input1_ - input2_;
        input1 = *(ull*)(&input1_);
        input2 = *(ull*)(&input2_);
        fn7 = fn7_;
        rm = rm_;
        if (fn7_ == FADD)
            expected_output = *(ull*)(&addition);
        else 
            expected_output = *(ull*)(&subtraction);
    }
};
queue<test_case_t> test_queue;
queue<ull> expected_output_queue;
double get_double1();
double get_double2();

double get_double1(){
    double min = -1.000000000000;//std::numeric_limits<double>::min();
    double max = 2.42000000000;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dis(min,max);
    return dis(gen);
}

double get_double2(){
    double min = -10000000000000000000000000000.0;//std::numeric_limits<double>::min();
    double max = 242000000000000000000000000000.0;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dis(min,max);
    return dis(gen);
}

int main(int argc, char **argv) {
    cout << "FP ADD Test" << endl;
    #pragma STDC FENV_ACCESS ON
    double total_error = 0.0;
    double delta = 0.0;
    int rm = 0;
    if (rm == 1) {
        std::fesetround(FE_TOWARDZERO);
    } else if (rm == 0){
        std::fesetround(FE_TONEAREST);
    } else if (rm == 3) {
        std::fesetround(FE_UPWARD);
    } else if (rm == 2) {
        std::fesetround(FE_DOWNWARD);
    }
    for (int i = 0; i < 1000000; i++) {
        double rs1 = get_double1();
        double rs2 = get_double2();
        double expected_output = rs1 - rs2;
        if (i%2 == 1) 
            test_queue.push(test_case_t(rs1, rs2, FSUB, rm));
        else 
            test_queue.push(test_case_t(rs1, rs2, FADD, rm));
        //cout.precision(20);
        //cout << i << " -- " << hex << "rs1: 0x" << *(ull*)(&rs1) << "(" << rs1 << ")" <<
        //"\trs2: 0x" << *(ull*)(&rs2) << "(" << rs2 << ")" <<
        //"\texpected_output: 0x" << *(ull*)(&expected_output) << endl;
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
    Vfp_add_simulation_wrapper *tb = new Vfp_add_simulation_wrapper;

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
                tb->rs1 =  *(ull*)(&test_queue.front().input1);
                tb->rs2 =  *(ull*)(&test_queue.front().input2);
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
                    cout << hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(double*)(&expected_output_queue.front()) << ")" 
                    << "\tOutput Received: 0x" << tb->rd << "(" << *(double*)(&tb->rd) << ")"
                    <<endl;
                    total_error += abs(*(double*)(&tb->rd) -  *(double*)(&expected_output_queue.front()));
                }// else {
                    //cout.precision(20);
                    //cout << test_count << ": " << 
                            //hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(double*)(&expected_output_queue.front()) << ")" 
                    //<< "\tOutput Received: 0x" << tb->rd << "(" << *(double*)(&tb->rd) << ")"
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
