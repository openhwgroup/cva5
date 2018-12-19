#include <stdlib.h>
#include <iostream>
#include "./obj_dir/Vver_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

using namespace std;

int main(int argc, char **argv) {
	// Initialize Verilators variables
	Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

	//VerilatedVcdC	*tracer;
	//tracer = new VerilatedVcdC;
	// Create an instance of our module under test
	Vver_top *tb = new Vver_top;
	//tb->trace(tracer, 99);
	//tracer->open("sim_results.vcd");

	cout << "Starting test\n";
	cout << "******************************\n";
	int reset_count = 0;
	long int cycle_cout = 0;
	tb->rst = 1;
	// Tick the clock until we are done
	while(!Verilated::gotFinish()) {
		if (reset_count > 64) {
			tb->rst = 0;
		}
		else {
			reset_count++;
		}

		tb->clk = 1;
		tb->eval();
		tb->clk = 0;
		tb->eval();

		if (tb->write_uart) {
			cout << tb->uart_byte;
		}

		if (tb->dec_instruction == 0x00100013U) {
			break;
		}
		//tracer->dump(vluint64_t(cycle_cout));
		cycle_cout++;
	}
	//tracer->flush();
	//tracer->close();
	cout << "******************************\n";
	cout << "Test Done\n";
	cout << "Simulated: " << cycle_cout << " cycles.";

	delete tb;
	exit(EXIT_SUCCESS);

}
