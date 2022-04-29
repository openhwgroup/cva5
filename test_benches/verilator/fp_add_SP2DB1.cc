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
#include "home/yuhuig/Data-Structure/Random.h"

#define TRACE_ON
#define FADD_DB 0b0000001
#define FSUB_DB 0b0000101
#define FADD_SP 0b0000000
#define FSUB_SP 0b0000100
using namespace std;
typedef unsigned long long int ull;
int i = 0;

struct test_case_t {
    ull input1;
    ull input2;
    int DB_fn7;
    int SP_fn7;
    int rm;
    int is_double;
    ull expected_output;
    test_case_t (double DB_rs1, double DB_rs2, float SP1_rs1, float SP1_rs2, float SP2_rs1, float SP2_rs2, int DB_fn7_, int SP_fn7_, int rm_, int is_double_) {
        #pragma STDC FENV_ACCESS ON
        if (rm_ == 1) {
            std::fesetround(FE_TOWARDZERO);
        } else if (rm == 0){
            std::fesetround(FE_TONEAREST);
        } else if (rm == 3) {
            std::fesetround(FE_UPWARD);
        } else if (rm == 2) {
            std::fesetround(FE_DOWNWARD);
        }
    
        if (is_double_) {
            double DB_expected_output=0.0;
            std::string op;
            if (DB_fn7_ == FADD_DB){ 
                DB_expected_output = DB_rs1 + DB_rs2;
                op = "ADD";
            } else {
                DB_expected_output = DB_rs1 - DB_rs2;
                op = "SUB";
            }
            input1 = *(ull*)(&DB_rs1);
            input2 = *(ull*)(&DB_rs2);
            expected_output = *(ull*)(&DB_expected_output);
            cout.precision(20);
            cout << i << "-DB-" << op << ": -- " << hex << "rs1: 0x" << input1 << "(" << *(double*)(&input1) << ")" <<
            "\trs2: 0x" << input2 << "(" << *(double*)(&input2) << ")" <<
            "\texpected_output: 0x" << expected_output << "(" << *(double*)(&expected_output) << ")" << endl;
        } else {
            float SP1_result;
            float SP2_result;
            unsigned int SP1_rs1_hex, SP1_rs2_hex, SP2_rs1_hex, SP2_rs2_hex;
            std:string op;
            if (SP_fn7_ == FADD_SP){
                SP1_result = SP1_rs1 + SP1_rs2;
                SP2_result = SP2_rs1 + SP2_rs2;
                op = "ADD";
            } else {
                SP1_result = SP1_rs1 - SP1_rs2;
                SP2_result = SP2_rs1 - SP2_rs2;
                op = "SUB";
            }
            SP1_rs1_hex = *(unsigned int*)(&SP1_rs1);
            SP1_rs2_hex = *(unsigned int*)(&SP1_rs2);
            SP2_rs1_hex = *(unsigned int*)(&SP2_rs1);
            SP2_rs2_hex = *(unsigned int*)(&SP2_rs2);
            input1 = ((*(ull*)(&SP2_rs1_hex)) << 32) | ((*(ull*)(&SP1_rs1_hex)) & 0x00000000ffffffff);
            input2 = ((*(ull*)(&SP2_rs2_hex)) << 32) | ((*(ull*)(&SP1_rs2_hex)) & 0x00000000ffffffff);
            //cout << hex << ((*(ull*)(&SP2_rs1_hex)) << 32) << "|" << ((*(ull*)(&SP2_rs2_hex)) << 32) << endl;
            //cout << hex << ((*(ull*)(&SP1_rs1_hex)) & 0x00000000ffffffff) << "|" << ((*(ull*)(&SP1_rs2_hex)) & 0x00000000ffffffff) << endl;
            //cout << hex << SP2_rs1_hex << "|" << SP1_rs1_hex << "; " << SP2_rs2_hex << "|" << SP1_rs2_hex << endl;
            //cout << hex << input1 << " " << input2 << endl;
            expected_output = ull(*(unsigned int*)(&SP2_result)) << 32 | ull(*(unsigned int*)(&SP1_result)); 
            cout.precision(10);
            cout << i << "-SP-" << op << ": --" << hex
                << " SP2: 0x" << hex << *(unsigned int*)(&SP2_rs1) << "(" << defaultfloat << SP2_rs1 << ")"
                << " 0x" << hex << *(unsigned int*)(&SP2_rs2) << "(" << defaultfloat << SP2_rs2 << ")" 
                << " sp2_result: 0x" << hex << *(unsigned int*)(&SP2_result) << "(" << SP2_result << ") ----- "
                 << " SP1: 0x" << *(unsigned int*)(&SP1_rs1) << "(" << defaultfloat << SP1_rs1 << ")"
                 << " 0x" << hex << *(unsigned int*)(&SP1_rs2) << "(" << defaultfloat << SP1_rs2 << ")"
                 << " sp1_result: 0x" << hex << *(unsigned int*)(&SP1_result) << "(" << SP1_result << ")"
                 "\texpected_output: 0x" << hex <<  expected_output << endl; 
        }
        
        DB_fn7 = DB_fn7_;
        SP_fn7 = SP_fn7_;
        is_double = is_double_;
        rm = rm_;
    }
};

queue<test_case_t> test_queue;
queue<ull> expected_output_queue;
double get_double();
float get_single1();
float get_single2();
vector<int> DB_fn7{FADD_DB, FSUB_DB};
vector<int> SP_fn7{FADD_SP, FSUB_SP};
vector<int> failed_tests;
queue<int> is_double_queue;

double get_double(){
    double min = -1.000000000000;//std::numeric_limits<double>::min();
    double max = 2.42000000000;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dis(min,max);
    return dis(gen);
}

float get_single1(){
    float min = -10000000000000000.0;//std::numeric_limits<double>::min();
    float max = 242000000000000000.0;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<float> dis(min,max);
    return dis(gen);
}

float get_single2(){
    float min = -10000000000000000.0;//std::numeric_limits<double>::min();
    float max = 242000000000000000.0;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<float> dis(min,max);
    return dis(gen);
}

int main(int argc, char **argv) {
    Random<ull> rand_ull;
    cout << "FP ADD MP Test" << endl;
    double total_error = 0.0;
    double delta = 0.0;
    int rm = 0;
    int DB_fn7_val, SP_fn7_val;
    int is_double;
    for (i = 0; i < 100000; i++) {
        is_double = (i+1)%2;
        DB_fn7_val = DB_fn7[(i+1)%2];
        SP_fn7_val = SP_fn7[(i+1)%2];
        double DB_rs1 = get_double();
        double DB_rs2 = get_double();
        float SP1_rs1 = get_single1();
        float SP1_rs2 = get_single2();
        float SP2_rs1 = get_single1();
        float SP2_rs2 = get_single2();
        test_queue.push(test_case_t(DB_rs1, DB_rs2, SP1_rs1, SP1_rs2, SP2_rs1, SP2_rs2, DB_fn7_val, SP_fn7_val, rm, is_double));
    }
    ofstream logFile, sigFile;
    bool logPhase; //Log phase vs signature phase used for compliance tests
    bool stallDetected = false;
    bool testFailed    = false;
    int stall_cycles   = 0;
    int test_count     = 0;

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
                test_case_t curr_test = test_queue.front();
                tb->new_request = 1;
                tb->is_double = curr_test.is_double;
                tb->rs1 =  (curr_test.input1);
                tb->rs2 =  (curr_test.input2);
                tb->DB_fn7 =  curr_test.DB_fn7;
                tb->SP1_fn7 = tb->SP2_fn7 = curr_test.SP_fn7;
                tb->DB_rm = curr_test.rm = tb->SP1_rm = tb->SP2_rm;

                is_double_queue.push(curr_test.is_double);
                expected_output_queue.push(curr_test.expected_output);
                test_queue.pop();
            }
            else {
                tb->new_request = 0;
                tb->rs1 = 0;
                tb->rs2 = 0;
            }

            //Recieve Output
            if(tb->done){
                if (is_double_queue.front()) {
                    if (expected_output_queue.front() != tb->rd){
                        testFailed = true;
                        cout.precision(20);
                        cout << "DB Test Failed " << test_count <<endl;;
                        cout << hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(double*)(&expected_output_queue.front()) << ")" 
                            << "\tOutput Received: 0x" << tb->rd << "(" << *(double*)(&tb->rd) << ")"
                            <<endl;
                        failed_tests.push_back(test_count);
                    } else {
                    cout.precision(20);
                    cout << "DB Test Passed " << test_count << ": "  
                    //<<hex << "Expected Output: 0x" << expected_output_queue.front() << "("<< *(double*)(&expected_output_queue.front()) << ")" 
                    //<< "\tOutput Received: 0x" << tb->rd << "(" << *(double*)(&tb->rd) << ")"
                    <<endl;
                    }
                } else {
                    ull SP_results = expected_output_queue.front();
                    ull received = tb->rd;
                    unsigned int SP1_result = (unsigned int) SP_results;
                    unsigned int SP2_result = (unsigned int) (SP_results >> 32);
                    unsigned int received_SP1_result = (unsigned int) received;
                    unsigned int received_SP2_result = (unsigned int) (received >> 32);
                    if (received != SP_results) {
                        testFailed = true;
                        cout.precision(10);
                        cout << "SP Test Failed " << test_count <<endl;
                        cout << hex << "Expected_SP2 0x" << SP2_result << "("<< *(float*)(&SP2_result) << ")" << "\tReceived_SP2 0x" << (unsigned int)(received_SP2_result) << "(" << *(float*)(&received_SP2_result) << ")" << "\t----- " 
                            << "\tExpected_SP1 0x" << SP1_result << "("<< *(float*)(&SP1_result) << ")" << "\tReceived_SP1 0x" << (unsigned int)(received_SP1_result) << "(" << *(float*)(&received_SP1_result) << ")" 
                            <<endl;
                        failed_tests.push_back(test_count);
                    } else {
                        cout.precision(10);
                        cout << "SP Test Passed " << test_count << endl;
                    }
                }
                cout << endl << endl;
                expected_output_queue.pop();
                is_double_queue.pop();
                if (expected_output_queue.size() == 0 && test_queue.size() == 0 && stall_cycles > 2){
                    break;
                } else {
                    stall_cycles ++;
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
    cout << "Failed test cases" <<endl; 
    for (int ele: failed_tests) {
        cout << ele << "\t";
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

