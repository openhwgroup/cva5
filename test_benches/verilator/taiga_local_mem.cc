#include <stdlib.h>
#include <iostream>
#include <fstream>
#include "Vtaiga_local_mem.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "TaigaTracer.h"

using namespace std;
int main(int argc, char **argv) {
    TaigaTracer<Vtaiga_local_mem> *taigaTracer;
    ofstream logFile, sigFile;

	// Initialize Verilators variables
	Verilated::commandArgs(argc, argv);

    if (!argv[1]) {
    	cout << "Missing log file name.\n";
    	exit(EXIT_FAILURE);
    }

    if (!argv[2]) {
    	cout << "Missing signature file name.\n";
    	exit(EXIT_FAILURE);
    }

    if (!argv[3]) {
    	cout << "Missing trace log file name.\n";
    	exit(EXIT_FAILURE);
    }

    logFile.open (argv[1]);
    sigFile.open (argv[2]);

    if (!logFile.is_open()) {
    	cout << "Failed to open logfile: " << argv[1] << endl;
    	exit(EXIT_FAILURE);
    }
    if (!sigFile.is_open()) {
    	cout << "Failed to open sigFile: " << argv[2] << endl;
    	exit(EXIT_FAILURE);
    }

	// Create an instance of our module under test
    taigaTracer = new TaigaTracer<Vtaiga_local_mem>;
    taigaTracer->set_log_file(&logFile);
    #ifdef TRACE_ON
        taigaTracer->start_tracer(argv[3]);
	#endif
	cout << "--------------------------------------------------------------\n";
	cout << "   Starting Simulation, logging to: " << argv[1] << "\n";
	cout << "--------------------------------------------------------------\n";

	// Tick the clock until we are done
	while(!(taigaTracer->has_stalled() || taigaTracer->has_terminated())) {
	    taigaTracer->tick();

        //Compliance Tests Signature Printing Phase
        if (taigaTracer->check_instruction_issued(COMPLIANCE_SIG_PHASE_NOP)) {
            std::cout << "\n--------------------------------------------------------------\n";
            std::cout << "                   Signature\n";
            std::cout << "--------------------------------------------------------------\n";
            taigaTracer->set_log_file(&sigFile);
        }
	}

	cout << "--------------------------------------------------------------\n";
	cout << "   Simulation Completed:  " << taigaTracer->get_cycle_count() << " cycles.\n";
    taigaTracer->print_stats();

	logFile.close();
	sigFile.close();

	delete taigaTracer;

	exit(EXIT_SUCCESS);
}
