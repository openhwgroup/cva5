#include <stdlib.h>
#include <iostream>
#include <fstream>
#include "Vtaiga_full_sim.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

//#define TRACE_ON

#define COMPLIANCE_SIG_PHASE_NOP 0x00B00013U
#define ERROR_TERMINATION_NOP 0x00F00013U
#define SUCCESS_TERMINATION_NOP 0x00A00013U
////////////////////////////////////////////////////
//Trace Interface Counters

struct TaigaTrace {
    static void TaigaTrace::update_stats(Vtaiga_full_sim *tb) {
        operand_stall += tb->operand_stall;
        unit_stall += tb->unit_stall;
        no_id_stall += tb->no_id_stall;
        no_instruction_stall += tb->no_instruction_stall;
        other_stall += tb->other_stall;

        instruction_issued_dec += tb->instruction_issued_dec;
        branch_misspredict += tb->branch_misspredict;
        return_misspredict += tb->return_misspredict;
        wb_mux_contention += tb->wb_mux_contention;

        rs1_forwarding_needed += tb->rs1_forwarding_needed;
        rs2_forwarding_needed += tb->rs2_forwarding_needed;
        rs1_and_rs2_forwarding_needed += tb->rs1_and_rs2_forwarding_needed;
    }

    static void print_stats(std::ostream& os) {
	    os << "   Taiga trace stats:\n";
	    os << "--------------------------------------------------------------\n";
	    os << "    operand_stall: " << operand_stall  << "\n";
	    os << "    unit_stall: " << unit_stall  << "\n";
	    os << "    no_id_stall: " << no_id_stall  << "\n";
	    os << "    no_instruction_stall: " << no_instruction_stall  << "\n";
	    os << "    other_stall: " << other_stall  << "\n";
	    os << "    instruction_issued_dec: " << instruction_issued_dec  << "\n";
	    os << "    branch_misspredict: " << branch_misspredict  << "\n";
	    os << "    return_misspredict: " << return_misspredict  << "\n";
	    os << "    wb_mux_contention: " << wb_mux_contention  << "\n";
	    os << "    rs1_forwarding_needed: " << rs1_forwarding_needed  << "\n";
	    os << "    rs2_forwarding_needed: " << rs2_forwarding_needed  << "\n";
	    os << "    rs1_OR_rs2_forwarding_needed: " << rs1_forwarding_needed + rs2_forwarding_needed  << "\n";
	    os << "    rs1_AND_rs2_forwarding_needed: " << rs1_and_rs2_forwarding_needed  << "\n";
	    os << "--------------------------------------------------------------\n\n";
    }

    static uint64_t operand_stall;
    static uint64_t unit_stall;
    static uint64_t no_id_stall;
    static uint64_t no_instruction_stall;
    static uint64_t other_stall;
    static uint64_t instruction_issued_dec;
    static uint64_t branch_misspredict;
    static uint64_t return_misspredict;
    static uint64_t wb_mux_contention;
    static uint64_t rs1_forwarding_needed;
    static uint64_t rs2_forwarding_needed;
    static uint64_t rs1_and_rs2_forwarding_needed;
};
Vtaiga_local_mem
#define STALL_LIMIT 2000

bool hasStalled(Vtaiga_full_sim *tb) {
    if (!tb->instruction_issued_dec) {
        stall_cycles++;
        if (stall_cycles > STALL_LIMIT) {
            stall_cycles = 0;
            std::cout << "\n\nError!!!!\n";
            std::cout << "PC unchanged for at least " << STALL_LIMIT << " cycles!\n\n";
            return true;
		} else {
			stall_cycles = 0;
		}
	}
	return false;
}

bool complianceTestsLogPhase; //Log phase vs signature phase used for compliance tests
bool checkForControlNOPs(Vtaiga_full_sim *tb) {
    //Custom nop to change to signature phase for compliance tests
    if (tb->instruction_data_dec == COMPLIANCE_SIG_PHASE_NOP && tb->instruction_issued_dec) {
        complianceTestsLogPhase = false;
        std::cout << "\n--------------------------------------------------------------\n";
        std::cout << "                   Signature\n";
        std::cout << "--------------------------------------------------------------\n";
        return false;
    }//Custom nop for error termination
    else if (tb->instruction_data_dec == ERROR_TERMINATION_NOP && tb->instruction_issued_dec) {
        std::cout << "\n\nError!!!!\n\n";
    }//Custom nop for regular termination
    else if (tb->instruction_data_dec == SUCCESS_TERMINATION_NOP && tb->instruction_issued_dec) {
    }

    return true;
}

void performReset(Vtaiga_full_sim *tb, int numCycles) {
    int reset_count = 0;
    tb->rst = 1;

	while(!Verilated::gotFinish()) {
		if (reset_count > numCycles) {
			tb->rst = 0;
			return;
		}
		else {
			reset_count++;
		}

		tb->clk = 1;
		tb->eval();
		tb->clk = 0;
		tb->eval();
	}
}

void handleUART(Vtaiga_full_sim *tb, bool logPhase, ofstream& logFile, ofstream& sigFile) {
	if (tb->write_uart) {
		std::cout <<  tb->uart_byte;
		if (logPhase) {
			logFile << tb->uart_byte;
		} else {
			sigFile << tb->uart_byte;
		}
	}
}

using namespace std;
int main(int argc, char **argv) {
	uint64_t cycle_cout = 0;
    TaigaTrace taigaTracer = { };//Zero initialize
    ofstream logFile, sigFile;

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
	Vtaiga_full_sim *tb = new Vtaiga_full_sim;

	#ifdef TRACE_ON
		VerilatedVcdC	*verilatorWaveformTracer;
		verilatorWaveformTracer = new VerilatedVcdC;
		tb->trace(verilatorWaveformTracer, 99);
		verilatorWaveformTracer->open("/data/sim-logs/sim_results.vcd");
	#endif

	cout << "--------------------------------------------------------------\n";
	cout << "   Starting Simulation, logging to: " << argv[1] << "\n";
	cout << "--------------------------------------------------------------\n";

    complianceTestsLogPhase = true;
    performReset(tb, 64);

	// Tick the clock until we are done
	while(!Verilated::gotFinish()) {
		tb->clk = 1;
		tb->eval();
		tb->clk = 0;
		tb->eval();

		cycle_cout++;
        taigaTracer.update_stats(tb);

        if (hasStalled(tb, cout)) break;
        if (checkForControlNOPs(tb)) break;
        handleUART(tb, complianceTestsLogPhase, logFile, sigFile);

		#ifdef TRACE_ON
				verilatorWaveformTracer->dump(vluint32_t(cycle_cout));
		#endif
	}

	#ifdef TRACE_ON
		verilatorWaveformTracer->flush();
		verilatorWaveformTracer->close();
	#endif

	cout << "--------------------------------------------------------------\n";
	cout << "   Simulation Completed:  " << cycle_cout << " cycles.\n";
    taigaTracer.print_stats(cout);

	logFile.close();
	sigFile.close();
	delete tb;
	exit(EXIT_SUCCESS);

}
