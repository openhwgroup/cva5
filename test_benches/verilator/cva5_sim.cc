#include <stdlib.h>
#include <iostream>
#include <fstream>
#include "verilated.h"
#include "verilated_fst_c.h"
#include "svdpi.h"
#include "Vcva5_sim__Dpi.h"
#include "Vcva5_sim.h"
#include "CVA5Tracer.h"

CVA5Tracer *cva5Tracer;
char* csv_log_name;
//For time index on assertions
 double sc_time_stamp () {
            return CVA5Tracer::get_cycle_count();
}

const char* cva5_csv_log_file_name () {
    return csv_log_name;
}

//#define TRACE_ON
using namespace std;
int main(int argc, char **argv) {
    ofstream logFile, sigFile, pcFile;
    ifstream programFile[1];

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
    programFile[0].open (argv[3]);

    if (!logFile.is_open()) {
        cout << "Failed to open logfile: " << argv[1] << endl;
        exit(EXIT_FAILURE);
    }
    if (!sigFile.is_open()) {
        cout << "Failed to open sigFile: " << argv[2] << endl;
        exit(EXIT_FAILURE);
    }

    char default_csv = '\0';
    if (argv[6]) {
        csv_log_name = argv[6];
    } else {
        csv_log_name = &default_csv; 
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
    cout << "   Simulation Completed\n";
    cout << "--------------------------------------------------------------\n";

    logFile.close();
    sigFile.close();
    programFile[0].close();
    pcFile.close();

    delete cva5Tracer;

    exit(EXIT_SUCCESS);
}
