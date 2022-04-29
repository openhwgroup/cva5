#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <cstdlib>
#include "Vfp_sign_inj_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <random>
#include <limits>

#define TRACE_ON
#define J 0
#define JN 1
#define JX 2
using namespace std;
typedef unsigned long long int ull;

struct test_case_t {
    ull input1;
    double input2;
    int rm;
    ull expected_output;
    test_case_t (double rs1, double rs2, int rm_) {
        input1 = *(ull*)(&rs1);
        input2 = rs2;
        rm = rm_;
        double result;
        bool rs1_sign = rs1 > 0.0 ? 0 : 1;
        bool rs2_sign = rs2 > 0.0 ? 0 : 1;
        if (rm == 0) {
            if (rs2_sign == 0){
                result = abs(rs1);
            } else {
                result = -abs(rs1);
            }
        } else if (rm == 1) {
            if (rs2_sign == 0){
                result = -abs(rs1);
            } else {
                result = abs(rs1);
            }
        } else if (rm = 2){
            if (rs2_sign^rs1_sign == 0){
                result = abs(rs1);
            } else {
                result = -abs(rs1);
            }
        }
        expected_output = *(ull*)(&result);
    }
};
queue<test_case_t> test_queue;
queue<ull> expected_output_queue;
double get_double();

double get_double(){
    double min = -10000.0;//std::numeric_limits<double>::min();
    double max = 10000.0;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dis(min,max);
    return dis(gen);
}

int main(int argc, char **argv) {
    for (int i = 0; i < 10; i++) {
        double rs1 = get_double();
        double rs2 = get_double();
        int rm = JX;
        test_queue.push(test_case_t(rs1, rs2, rm));

        double result;
        bool rs1_sign = rs1 > 0.0 ? 0 : 1;
        bool rs2_sign = rs2 > 0.0 ? 0 : 1;
        if (rm == 0) {
            if (rs2_sign == 0){
                result = abs(rs1);
            } else {
                result = -abs(rs1);
            }
        } else if (rm == 1) {
            if (rs2_sign == 0){
                result = -abs(rs1);
            } else {
                result = abs(rs1);
            }
        } else if (rm = 2){
            if (rs2_sign^rs1_sign == 0){
                result = abs(rs1);
            } else {
                result = -abs(rs1);
            }
        }
        cout << i << " -- " << hex << "rs1: 0x" << *(ull*)(&rs1) << "(" << rs1 << ")" <<
        "\trs2_sign: " << rs2_sign << 
        "\texpected_output: " << dec << result << 
        endl;
    }

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
    Vfp_sign_inj_simulation_wrapper *tb = new Vfp_sign_inj_simulation_wrapper;

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
                tb->rs2_sign =  *(double*)(&test_queue.front().input2) > 0.0 ? 0 : 1;
                tb->rm = test_queue.front().rm;
                expected_output_queue.push(test_queue.front().expected_output);
                test_queue.pop();
            }
            else {
                tb->new_request = 0;
                tb->rs1 = 0;
                tb->rs2_sign = 0;
            }

            //Recieve Output
            if(tb->done){
                cout << "tb->done =" << tb->done << endl;
                if (expected_output_queue.front() != tb->rd){
                    testFailed = true;
                    cout << "Test Failed " << test_count <<endl;;
                    cout << hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(double*)(&expected_output_queue.front()) << ")" 
                    << "\tOutput Received: 0x" << tb->rd << "(" << *(double*)(&tb->rd) << ")"
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

    #ifdef TRACE_ON
	    tracer->flush();
	    tracer->close();
    #endif

    logFile.close();
    sigFile.close();
    delete tb;
    exit(EXIT_SUCCESS);


}
