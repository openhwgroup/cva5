#ifndef unit_test_H
#define unit_test_H
#include <fstream>
#include <iostream>
#include <queue>
#include <iomanip>
#include <stdlib.h>
#include <stdint.h>

template <class TB, typename INT, typename FLOAT>
class unit_test {
    public: 
        int reset_length;
        int cycle_count;
        int instruction_cycle;
        unit_test(const char *input_file, int input_count, const char *output_file);
        ~unit_test();
        void tick();
        void reset();
        void start_tracer(const char *tracer_file);
        void read_inputs(); //read alraedy generated input pairs 
        void GenInputs();
        INT div(INT rs1, INT rs2);
        INT sqrt_custom(FLOAT rs1);
        void print_inputs();
        void verify();
        void drive_inputs();
        bool terminate();
        void faulty_output_log();
        INT xoshiro256ss(struct xoshiro256ss_state *state);
        struct test_case_t {
            INT rs1;
            INT rs2;
            int rm;
            int id;
            test_case_t (INT input1_, INT input2_) {
                rs1 = input1_;
                rs2 = input2_;
                rm = 0;
                id = 0;
            }
        };
        private:
        const char *inputs;
        const char *outputs;
        uint64_t seed[4];
        TB *tb;
        #ifdef TRACE_ON
        VerilatedVcdC *tracer;
        #endif
        std::queue<test_case_t> test_queue;
        std::queue<test_case_t> debug_queue;
        std::queue<INT> expected_output_queue;
        std::queue<test_case_t> wrong_result_queue;
        int input_count;
        int verify_count;
        bool ready;
        double accu_error;
};

#include "unit_test.cc"
#endif
