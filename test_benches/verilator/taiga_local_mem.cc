#include <stdlib.h>
#include <iostream>
#include <fstream>
#include "Vtaiga_local_mem.h"
#include "verilated.h"
#include "verilated_vcd_c.h"


using namespace std;
int main(int argc, char **argv) {
	  ofstream logFile, sigFile;
	  bool logPhase;
	  bool stallDetected = false;
	  int stall_cycles = 0;

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
	Vtaiga_local_mem *tb = new Vtaiga_local_mem;

	#ifdef TRACE_ON
		VerilatedVcdC	*tracer;
		tracer = new VerilatedVcdC;
		tb->trace(tracer, 99);
		tracer->open("sim_results.vcd");
	#endif

	cout << "\n\nStarting test: " << argv[2] << "\n";
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
		if (tb->dec_instruction_r == 0x00B00013U) {
			logPhase = false;
			cout << "******************************\n";
			cout << "\n\n**********Signature***********\n";
		}
		
		//if (!logPhase) {
		//	std::cout << std::hex << tb-> dec_pc_debug_r << std::endl;
		//}
		
		
		if (tb->write_uart) {
			if (logPhase) {
				cout <<  tb->uart_byte;
				logFile << tb->uart_byte;
			} else {
				cout <<  tb->uart_byte;
				sigFile << tb->uart_byte;
			}
		}

		//Custom nop for termination
		if (tb->dec_instruction_r == 0x00F00013U) {
			cout << "\n\nError!!!!\n\n";
			break;
		}
		else if (tb->dec_instruction_r == 0x00A00013U) {
			break;
		}
		#ifdef TRACE_ON
				tracer->dump(vluint64_t(cycle_cout));
		#endif
		cycle_cout++;

		if (!tb->dec_advance_debug) {
			stall_cycles++;
			if (stall_cycles > 2000) {
				stall_cycles = 0;
				cout << "\n\nError!!!!\n";
				cout << "PC unchanged for at least 2000 cycles!\n\n";
				break;
			}
		} else {
			stall_cycles = 0;
		}

	}

	#ifdef TRACE_ON
		tracer->flush();
		tracer->close();
	#endif

	cout << "\n******************************\n\n";
	cout << "Test Done\n";
	cout << "Simulated: " << cycle_cout << " cycles.\n\n\n";

	logFile.close();
	sigFile.close();
	delete tb;
	exit(EXIT_SUCCESS);

}
