#include <stdlib.h>
#include <iostream>
#include <fstream>
#include "Vtaiga_local_mem.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

////////////////////////////////////////////////////
//Trace Interface Counters
uint64_t operand_stall = 0;
uint64_t unit_stall = 0;
uint64_t no_id_stall = 0;
uint64_t no_instruction_stall = 0;
uint64_t other_stall = 0;
uint64_t instruction_issued_dec = 0;
uint64_t branch_misspredict = 0;
uint64_t return_misspredict = 0;


using namespace std;
int main(int argc, char **argv) {
	  ofstream logFile, sigFile;
	  bool logPhase; //Log phase vs signature phase used for compliance tests
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

	cout << "--------------------------------------------------------------\n";
	cout << "  Starting Simulation, logging to: " << argv[1] << "\n";
	cout << "--------------------------------------------------------------\n";
	int reset_count = 0;
	uint64_t cycle_cout = 0;
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

        if (reset_count > 64) {
            operand_stall += tb->operand_stall ? 1 : 0;
            unit_stall += tb->unit_stall ? 1 : 0;
            no_id_stall += tb->no_id_stall ? 1 : 0;
            no_instruction_stall += tb->no_instruction_stall ? 1 : 0;
            other_stall += tb->other_stall ? 1 : 0;

            instruction_issued_dec += tb->instruction_issued_dec ? 1 : 0;
            branch_misspredict += tb->branch_misspredict ? 1 : 0;
            return_misspredict += tb->return_misspredict ? 1 : 0;
        }


		//Custom nop to change to signature phase for compliance tests
		if (tb->instruction_data_dec == 0x00B00013U) {
			logPhase = false;
			cout << "\n--------------------------------------------------------------\n";
			cout << "                   Signature\n";
			cout << "--------------------------------------------------------------\n";
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

		//Custom nop for error termination
		if (tb->instruction_data_dec == 0x00F00013U) {
			cout << "\n\nError!!!!\n\n";
			break;
		}//Custom nop for regular termination
		else if (tb->instruction_data_dec == 0x00A00013U) {
			break;
		}
		#ifdef TRACE_ON
				tracer->dump(vluint32_t(cycle_cout));
		#endif
		cycle_cout++;

		if (!tb->instruction_issued_dec) {
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

	cout << "\n--------------------------------------------------------------\n";
	cout << "  Simulation Completed:  " << cycle_cout << " cycles.\n";
	cout << "--------------------------------------------------------------\n";

	cout << "\n\n--------------------------------------------------------------\n";
	cout << "Taiga trace stats:\n";
	cout << "--------------------------------------------------------------\n";
	cout << "operand_stall: " << operand_stall  << "\n";
	cout << "unit_stall: " << unit_stall  << "\n";
	cout << "no_id_stall: " << no_id_stall  << "\n";
	cout << "no_instruction_stall: " << no_instruction_stall  << "\n";
	cout << "other_stall: " << other_stall  << "\n";
	cout << "instruction_issued_dec: " << instruction_issued_dec  << "\n";
	cout << "branch_misspredict: " << branch_misspredict  << "\n";
	cout << "return_misspredict: " << return_misspredict  << "\n";
	cout << "--------------------------------------------------------------\n";

	logFile.close();
	sigFile.close();
	delete tb;
	exit(EXIT_SUCCESS);

}
