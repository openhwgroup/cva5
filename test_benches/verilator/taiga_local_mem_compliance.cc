#include <stdlib.h>
#include <iostream>
#include <fstream>
#include "Vtaiga_local_mem_compliance.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

using namespace std;
int main(int argc, char **argv) {
	  ofstream logFile;
	  bool logPhase;
	// Initialize Verilators variables
	Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    if (!argv[1]) {
    	cout << "Missing log file name.\n";
    	exit(EXIT_FAILURE);
    }

    logFile.open (argv[1]);
	//VerilatedVcdC	*tracer;
	//tracer = new VerilatedVcdC;
	// Create an instance of our module under test
	Vtaiga_local_mem_compliance *tb = new Vtaiga_local_mem_compliance;
	//tb->trace(tracer, 99);
	//tracer->open("sim_results.vcd");

	cout << "Starting test\n";
	cout << "******************************\n";
	int reset_count = 0;
	long int cycle_cout = 0;
	tb->rst = 1;
    logPhase = true;

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


		//Custom nop to change to signature phase
		if (tb->dec_instruction_r == 0x00200013U) {
			logPhase = false;
		}

		if (tb->write_uart) {
			if (logPhase)
				logFile << tb->uart_byte;
			else
				cout << tb->uart_byte;
		}

		//Custom nop for termination
		if (tb->dec_instruction_r == 0x00100013U) {
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

	logFile.close();
	delete tb;
	exit(EXIT_SUCCESS);

}
