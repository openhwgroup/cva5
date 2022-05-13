#include <stdlib.h>
#include <iostream>
#include <fstream>
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vcva5_sim.h"
#include "CVA5Tracer.h"

CVA5Tracer *cva5Tracer;

//For time index on assertions
 double sc_time_stamp () {
            return cva5Tracer->get_cycle_count();
}

//#define TRACE_ON
using namespace std;
int main(int argc, char **argv) {
    ofstream logFile, sigFile, pcFile;
    ifstream programFile;

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
    	cout << "Missing program file name.\n";
    	exit(EXIT_FAILURE);
    }

    if (!argv[4]) {
    	cout << "Missing trace log file name.\n";
    	exit(EXIT_FAILURE);
    }



    logFile.open (argv[1]);
    sigFile.open (argv[2]);
    //printf("HW INIT:%s \n", argv[3]);
    programFile.open (argv[3]);

    if (!logFile.is_open()) {
    	cout << "Failed to open logfile: " << argv[1] << endl;
    	exit(EXIT_FAILURE);
    }
    if (!sigFile.is_open()) {
    	cout << "Failed to open sigFile: " << argv[2] << endl;
    	exit(EXIT_FAILURE);
    }

	// Create an instance of our module under test
    cva5Tracer = new CVA5Tracer(programFile);
    cva5Tracer->set_log_file(&logFile);

    if (argv[5]) {
        pcFile.open (argv[5]);
    }
    if (pcFile.is_open()) {
        cva5Tracer->set_pc_file(&pcFile);
    }

    #ifdef TRACE_ON
        cva5Tracer->start_tracer(argv[4]);
	#endif
	cva5Tracer->reset();
	cout << "--------------------------------------------------------------\n";
	cout << "   Starting Simulation, logging to " << argv[1] << "\n";
	cout << "--------------------------------------------------------------\n";
    cout << flush;

	// Tick the clock until we are done
    bool sig_phase_complete = false;
	while(!(cva5Tracer->has_stalled() || cva5Tracer->has_terminated())) {
	    cva5Tracer->tick();
        //Compliance Tests Signature Printing Phase
        sig_phase_complete |= cva5Tracer->check_if_instruction_retired(COMPLIANCE_SIG_PHASE_NOP);
        if (sig_phase_complete && cva5Tracer->store_queue_empty()) {
            std::cout << "\n--------------------------------------------------------------\n";
            std::cout << "                   Signature\n";
            std::cout << "--------------------------------------------------------------\n";
            cva5Tracer->set_log_file(&sigFile);
        }
	}

	cout << "--------------------------------------------------------------\n";
	cout << "   Simulation Completed  " << cva5Tracer->get_cycle_count() << " cycles.\n";
    cva5Tracer->print_stats();

	logFile.close();
	sigFile.close();
    programFile.close();
    pcFile.close();

	delete cva5Tracer;

	exit(EXIT_SUCCESS);
}
