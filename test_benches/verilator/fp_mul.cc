#include <cfenv>    
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <cstdlib>
#include "Vfp_mul_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <random>
#include <limits>

#define TRACE_ON
using namespace std;
typedef unsigned long long int ull;

struct test_case_t {
    ull input1;
    ull input2;
    int rm;
    ull expected_output;
    test_case_t (double input1_, double input2_, int rm_) {
        if (rm_ == 1) {
            std::fesetround(FE_TOWARDZERO);
        } else if (rm_ == 0){
            std::fesetround(FE_TONEAREST);
        } else if (rm_ == 3) {
            std::fesetround(FE_UPWARD);
        } else if (rm_ == 2) {
            std::fesetround(FE_DOWNWARD);
        } 
        double result = input1_ * input2_;
        input1 = *(ull*)(&input1_);
        input2 = *(ull*)(&input2_);
        rm = rm_;
        expected_output = *(ull*)(&result);
    }
};
queue<test_case_t> test_queue;
queue<ull> expected_output_queue;
double get_double1();
double get_double2();

double get_double1(){
    double min = -10000.0;
    double max = 10000.0;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dis(min,max);
    return dis(gen);
}
double get_double2(){
    double min = -0.0000000000000000000000000000000000000000001;
    double max = 0.000000000000000000000000000000; 

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dis(min,max);
    return dis(gen);
}


int main(int argc, char **argv) {
    cout << "FP Mul Test" <<endl;
    double total_error = 0.0;
    #pragma STDC FENV_ACCESS ON
    int rm = 4;
    if (rm == 1) {
        std::fesetround(FE_TOWARDZERO);
    } else if (rm == 0){
        std::fesetround(FE_TONEAREST);
    } else if (rm == 3) {
        std::fesetround(FE_UPWARD);
    } else if (rm == 2) {
        std::fesetround(FE_DOWNWARD);
    }
    for (int i = 0; i < 1000; i++) {
        double rs1 = get_double2();
        double rs2 = get_double2();
        double expected_output = rs1 * rs2;
        test_queue.push(test_case_t(rs1, rs2, rm));
        cout << i  << hex << 
        "\trs1: 0x" << *(ull*)(&rs1) << "(" << rs1 << ")" <<
        "\trs2: 0x" << *(ull*)(&rs2) << "(" << rs2 << ")" <<
        "\texpected_output: 0x" << *(ull*)(&expected_output) << "(" << expected_output << ")" << endl;
    }

    //test_queue.push(test_case_t(0.000000000000000000000000000000000001, 0.000000000000000000000001, rm)); //different result from c++ implementation; taiga fpu is closer to exact result
    //double test1 = 0.000000000000000000000000000000000001;
    //double test2 = 0.000000000000000000000001;
    //double result = 0;
    //test_queue.push(test_case_t(*(double*)(&test1), *(double*)(&test2), rm));
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


    // double d = 1.5;
    // cout << hex << *(ull*)(&d) << endl;

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
    Vfp_mul_simulation_wrapper *tb = new Vfp_mul_simulation_wrapper;

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
                    << "\tDelta: " << *(double*)(&expected_output_queue.front()) - *(double*)(&tb->rd) 
                    <<endl;
                    total_error += *(double*)(&expected_output_queue.front()) - *(double*)(&tb->rd);
                } else {
                    cout.precision(20);
                    cout << "Test Passed " << test_count <<endl;;
                    cout << hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(double*)(&expected_output_queue.front()) << ")" 
                    << "\tOutput Received: 0x" << tb->rd << "(" << *(double*)(&tb->rd) << ")"
                    << "\tDelta: " << *(double*)(&expected_output_queue.front()) - *(double*)(&tb->rd) 
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
