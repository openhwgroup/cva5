#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <cstdlib>
#include "Vfp_new_cvt_simulation_wrapper.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <random>
#include <limits.h>
#include <float.h>
#include <iomanip>

#define TRACE_ON
#define FADD 0b0000001
#define FSUB 0b0000101
using namespace std;
typedef unsigned long long int ull;

struct test_case_t {
    ull f2i_input1;
    int i2f_input1;
    int rm;
    int is_float;
    int is_signed;
    int is_mv;
    double i2f_expected_output;
    int f2i_expected_output;
    test_case_t (double f2i_input1_, int i2f_input1_, int rm_, int is_float_, int is_mv_, int is_signed_, int i) {
        f2i_input1 = *(ull*)(&f2i_input1_);
        i2f_input1 = i2f_input1_; 
        rm = rm_;
        is_float = is_float_;
        is_mv = is_mv_;
        is_signed = is_signed_;
        i2f_expected_output = (double)(i2f_input1_);;
        f2i_expected_output = is_signed_ ? (int)(f2i_input1_) : (unsigned int)(f2i_input1_);
        if(is_float_){
            cout << i << ": " << "f2i_rs1: " << dec << f2i_input1_ << "\t(0x" << hex << *(ull*)(&f2i_input1_) << ")" << dec
                 << "\tExpected output: " << f2i_expected_output << endl;
        } else {
            cout << i << ": " << "i2f_rs1: " << dec << i2f_input1_
                 << "\tExpected Output: " << (double)i2f_input1_ << "\t(0x" << hex << *(ull*)(&i2f_expected_output) << ")" << endl;
        }
    }
};

struct expected_output_t
{
    double i2f_expected_output;
    int f2i_expected_output;
    int is_float;
    int is_signed;
    expected_output_t (double i2f, int f2i, int is_float, int is_signed){
        i2f_expected_output = i2f;
        f2i_expected_output = f2i;
        is_float = is_float;
        is_signed = is_signed;
    }
};

queue<test_case_t> test_queue;
queue<expected_output_t> expected_output_queue;
double get_double();
int get_signed_int();
unsigned int get_unsigned_int();

double get_double(){
    double min = -100000.0;//DBL_MIN;
    double max = 100000.0;//DBL_MAX;

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dis(min,max);
    return dis(gen);
}

double get_unsigned_double(){
    double min = 0.0;//std::numeric_limits<double>::min();
    double max = DBL_MAX;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dis(min,max);
    return dis(gen);
}


int get_signed_int(){
    int min = INT_MIN;//std::numeric_limits<double>::min();
    int max = INT_MAX;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dis(min,max);
    return dis(gen);
}

unsigned int get_unsigned_int(){
    int min = 0;//std::numeric_limits<double>::min();
    int max = INT_MAX;//std::numeric_limits<double>::max();

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<unsigned int> dis(min,max);
    return dis(gen);
}


int main(int argc, char **argv) {
    for (int i = 0; i < 10; i++) {
        int is_signed = 1;
        int is_float = 0;
        int is_mv = 0;
        int i2f_rs1;
        double f2i_rs1;
        if (is_signed == 1){
            i2f_rs1 = get_signed_int();
            f2i_rs1 = get_double();
        } else {
            i2f_rs1 = get_unsigned_int();
            f2i_rs1 = get_unsigned_double();
        }
        test_queue.push(test_case_t(f2i_rs1,i2f_rs1,1,is_float,is_mv,is_signed,i));
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
    Vfp_new_cvt_simulation_wrapper *tb = new Vfp_new_cvt_simulation_wrapper;

   #ifdef TRACE_ON
     cout << "Tracing" << endl;
      VerilatedVcdC *tracer;
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
            tb->fp_new_request = 0;
        } 
        else {
            tb->rst = 0;
            if (test_queue.size() == 0) {
                tb->new_request = 0;
                tb->fp_new_request = 0;
            }

            if (test_queue.size() != 0 && (tb->ready == 1 || tb->fp_ready == 1)){
                tb->new_request = (test_queue.front().is_float == 1);
                tb->fp_new_request = (test_queue.front().is_float == 0);
                tb->rm = test_queue.front().rm;
                tb->is_mv = test_queue.front().is_mv;
                tb->is_float = test_queue.front().is_float;
                tb->is_signed = test_queue.front().is_signed;
                tb->f2i_rs1 = test_queue.front().f2i_input1;
                tb->i2f_rs1 = test_queue.front().i2f_input1;
                expected_output_queue.push(expected_output_t(test_queue.front().i2f_expected_output,test_queue.front().f2i_expected_output,test_queue.front().is_float,test_queue.front().is_signed));
                test_queue.pop();
            }
            else {
                tb->new_request = 0;
                tb->fp_new_request = 0;
                tb->f2i_rs1 = 0;
                tb->i2f_rs1 = 0;
            }

            //Recieve Output
            // if(tb->done || tb->fp_done){
            //     if (test_queue.front().is_float) {
            //         if (expected_output_queue.front().f2i_expected_output != *(int*)(&tb->rd)) {
            //             testFailed = true;
            //             cout << dec << 
            //             "f2i Test Failed " << test_count <<endl;
            //             cout << dec << "Expected Output: " << expected_output_queue.front().f2i_expected_output << "(0x" << hex << (ull)(expected_output_queue.front().f2i_expected_output) 
            //             << dec << "\tOutput Received: " << (int)tb->rd  << hex << " 0x" << tb->rd
            //             <<endl;
            //         } else {
            //             testFailed = false;
            //             cout << "f2i Test Passed " << dec << test_count
            //             << endl;
            //             cout << dec << "Output Received: " << (int)tb->rd  << hex << " 0x" << tb->rd
            //             <<endl;
            //         }
            //     } else {
            //         if (expected_output_queue.front().i2f_expected_output != *(double*)(&tb->fp_rd)) {
            //             testFailed = true;
            //             cout << dec << 
            //             "i2f Test Failed " << test_count <<endl;
            //             cout << dec << "Expected Output: " << expected_output_queue.front().i2f_expected_output << "(0x" << hex << (ull)(expected_output_queue.front().i2f_expected_output) 
            //             << dec << "\tOutput Received: " << *(double*)(&tb->fp_rd)  << hex << " 0x" << tb->fp_rd
            //             <<endl;
            //         } else {
            //             testFailed = false;
            //             cout << "i2f Test Passed " << dec << test_count
            //             << endl;
            //             cout << dec << "Output Received: " << *(double*)(&tb->fp_rd)  << hex << " 0x" << tb->fp_rd
            //             <<endl;
            //         }
            //     }
            //     cout << endl << endl;
            //     expected_output_queue.pop();
            //     // printf("Expected output queue size %d\tTest queue size %d\n", expected_output_queue.size(), test_queue.size());
            //     // if (expected_output_queue.size() == 0 && test_queue.size() == 0)
            //     //     break;
            //     if (expected_output_queue.size() == 0 && test_queue.size() == 0){
            //         break;
            //     } else {
            //         stall_cycles++;
            //     }
            //     test_count++;
            // }
            if(tb->done) {
                //f2i
                if (expected_output_queue.front().f2i_expected_output != *(int*)(&tb->rd)) {
                        testFailed = true;
                        cout << dec << 
                        "f2i Test Failed " << test_count <<endl;
                        cout << dec << "Expected Output: " << expected_output_queue.front().f2i_expected_output << "(0x" << hex << (ull)(expected_output_queue.front().f2i_expected_output) 
                        << dec << "\tOutput Received: " << (int)tb->rd  << hex << " 0x" << tb->rd
                        <<endl;
                    } else {
                        testFailed = false;
                        cout << "f2i Test Passed " << dec << test_count
                        << endl;
                        cout << dec << "Output Received: " << (int)tb->rd  << hex << " 0x" << tb->rd
                        <<endl;
                    }
                    cout << endl << endl;
                    expected_output_queue.pop();
                    if (expected_output_queue.size() == 0 && test_queue.size() == 0){
                        break;
                    }
                    test_count++;
            } else if (tb->fp_done) {
                //i2f
                if (expected_output_queue.front().i2f_expected_output != *(double*)(&tb->fp_rd)) {
                        testFailed = true;
                        cout << dec << 
                        "i2f Test Failed " << test_count <<endl;
                        cout << dec << "Expected Output: " << expected_output_queue.front().i2f_expected_output << "(0x" << hex << (ull)(expected_output_queue.front().i2f_expected_output) 
                        << dec << "\tOutput Received: " << *(double*)(&tb->fp_rd)  << hex << " 0x" << tb->fp_rd
                        <<endl;
                    } else {
                        testFailed = false;
                        cout << "i2f Test Passed " << dec << test_count
                        << endl;
                        cout << dec << "Output Received: " << *(double*)(&tb->fp_rd)  << hex << " 0x" << tb->fp_rd
                        <<endl;
                    }
                    cout << endl << endl;
                    expected_output_queue.pop();
                    if (expected_output_queue.size() == 0 && test_queue.size() == 0){
                        break;
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
