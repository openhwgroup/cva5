#define DIV_SQRT_UNIT 1
#define IS_DIV 1

#include <stdlib.h>
#include <iostream>
#include <fstream>
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vfp_div_sqrt_simulation_wrapper.h"
#include "unit_test.h"

vluint64_t main_time = 0;
double sc_time_stamp () {
    return main_time;	 
}

typedef unsigned long long ull;

unit_test<Vfp_div_sqrt_simulation_wrapper, ull, double> *unit_test_inst;

int main(int argc, char ** argv) {
    if (!argv[1]) {
        std::cout << "missinh input file" << std::endl;
        exit(EXIT_FAILURE);
    }

    if (!argv[2]) {
        std::cout << "missing trace file" << std::endl;
        exit(EXIT_FAILURE);
    }

    if (!argv[3]) {
        std::cout << "missing input count" << std::endl;
        exit(EXIT_FAILURE);
    }

    if (!argv[4]) {
        std::cout << "missing output log" << std::endl;
        exit(EXIT_FAILURE);
    }
    int input_count = std::stoi(argv[3], NULL, 10);

    unit_test_inst = new unit_test<Vfp_div_sqrt_simulation_wrapper, ull, double>(argv[1], input_count, argv[4]);
    #ifdef TRACE_ON
        unit_test_inst->start_tracer(argv[2]);
	#endif
    //unit_test_inst->read_inputs();
    unit_test_inst->GenInputs();
    //unit_test_inst->print_inputs();

    unit_test_inst->reset();
    while (!unit_test_inst->terminate()) {
        unit_test_inst->tick();
    }

    delete unit_test_inst;
    exit(EXIT_SUCCESS);
    return 0;
}
