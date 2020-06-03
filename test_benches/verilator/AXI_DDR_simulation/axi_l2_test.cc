#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include "Vaxi_l2_test.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

////////////////////////////////////////////////////
//Trace Interface Counters
int num_entries = PAGE_SIZE * 5;
uint32_t starting_location = PAGE_SIZE*0;
struct l2_arb_inputs{
	uint32_t address;
	uint32_t rnw;
	uint32_t burst_length;
	uint32_t sub_id;
	uint32_t be;
};
struct l2_arb_expected_output{
	uint32_t rd_data;
	uint32_t rd_sub_id;
};

queue<l2_arb_inputs> test_inputs;
queue<l2_arb_expected_output> test_expected_output;
queue<uint32_t> test_data_inputs;

void assign_read_input(uint32_t address, uint32_t burst_length, uint32_t sub_id){
	l2_arb_inputs in_elem{address, 1, burst_length, sub_id};
	test_inputs.push(in_elem);
};

void assign_write_input(uint32_t address, uint32_t burst_length, uint32_t sub_id, uint32_t be){
	l2_arb_inputs in_elem{address, 0, burst_length, sub_id, be};
	test_inputs.push(in_elem);
	for(int i = burst_length-1 ; i >= 0; i--){
		test_data_inputs.push(i+71);
	}
};

void assign_single_write_input(uint32_t address, uint32_t sub_id, uint32_t data, uint32_t be){
	l2_arb_inputs in_elem{address, 0, 1, sub_id, be};
	test_inputs.push(in_elem);
	test_data_inputs.push(data);
	
};
vluint64_t main_time = 0; // Current simulation time
// This is a 64-bit integer to reduce wrap over issues and
// allow modulus. You can also use a double, if you wish.
double sc_time_stamp () { // Called by $time in Verilog
return main_time; // converts to double, to match
// what SystemC does
}

using namespace std;
int main(int argc, char **argv) {
	//assign_single_write_input(0,1, 1 ,0xF);
	//assign_single_write_input(0,0, 21 ,0xF);
	assign_single_write_input(4,0, 22 ,0xF);
	//assign_single_write_input(4,0, 23 ,0xF);
	//assign_single_write_input(4,0, 25 ,0xF);
	//assign_write_input(0, 4, 0, 0xF);
	assign_read_input(4, 4, 0);
	//assign_read_input(4, 8, 0);;
    ofstream logFile, sigFile;
	uint64_t cycle_cout = 0;

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
	Vaxi_l2_test *tb = new Vaxi_l2_test;
    axi_ddr_sim <Vaxi_l2_test>  axi_ddr("DDR_init.txt", starting_location, num_entries, tb);
	#ifdef TRACE_ON
		VerilatedVcdC	*verilatorWaveformTracer;
		verilatorWaveformTracer = new VerilatedVcdC;
		tb->trace(verilatorWaveformTracer, 99);
		verilatorWaveformTracer->open("/data/sim-logs/sim_results.vcd");
	#endif

	cout << "--------------------------------------------------------------\n";
	cout << "   Starting Simulation, logging to: " << argv[1] << "\n";
	cout << "--------------------------------------------------------------\n";

	//Reset 
	for(int i = 0; i < 50;i++){
		tb->rst = 1;

		tb->clk = 1;
		tb->eval();
		tb->clk = 0;
		tb->eval();
	}
		tb->rst = 0;
		tb->clk = 1;
		tb->eval();
		tb->clk = 0;
		tb->eval();
	// Tick the clock until we are done
	int number_of_data_left = 0;
	while(!Verilated::gotFinish()) {
		tb->clk = 1;
		tb->eval();

		//Specify Inputs
		//Note: Current doesn't give the arbiter the address and data separate 
		//READ Input
		if(test_inputs.size() > 0 && !tb->request_full && test_inputs.front().rnw){
			l2_arb_inputs elem;
			elem = test_inputs.front();
			test_inputs.pop();
			tb->addr = elem.address;
			tb->rnw = elem.rnw;
			tb->is_amo = 0;
			tb->amo_type_or_burst_size = elem.burst_length;
			tb->sub_id = elem.sub_id;
 
			tb->request_push = 1;
			tb->wr_data_push = 0;
		}
		else if(test_inputs.size() > 0 && !tb->request_full && !test_inputs.front().rnw && number_of_data_left == 0){
			l2_arb_inputs elem;
			elem = test_inputs.front();
			tb->addr = elem.address;
			tb->rnw = elem.rnw;
			tb->is_amo = 0;
			tb->amo_type_or_burst_size = elem.burst_length - 1;
			tb->sub_id = elem.sub_id;
			tb->be = elem.be;
			number_of_data_left = elem.burst_length;
			tb->request_push = 1;
			tb->wr_data_push = 0;
		}
		else if(number_of_data_left > 0){
			tb->request_push = 0;

			if(!tb->data_full){
				uint32_t data = test_data_inputs.front();
				test_data_inputs.pop();
				tb->wr_data = data;
				tb->wr_data_push = 1;

				number_of_data_left--;
				if(number_of_data_left == 0)
					test_inputs.pop();
			}
			else{
				tb->wr_data_push = 0;
			}

		}
		else{
			tb->addr = rand();
			tb->rnw = rand() % 2;
			tb->is_amo = rand() % 2;
			tb->amo_type_or_burst_size = rand();
			tb->sub_id = rand();
			tb->wr_data = rand();

			tb->request_push = 0;
			tb->wr_data_push = 0;
		}

		if(tb->rd_data_valid){
			tb->rd_data_ack = 1;
			cout << "Data Recieved: " << tb->rd_data << endl;
		}
		else{
			tb->rd_data_ack = 0;
		}
		//Step
		axi_ddr.step();

		tb->clk = 0;
		tb->eval();
		cycle_cout++;
		#ifdef TRACE_ON
				verilatorWaveformTracer->dump(vluint32_t(cycle_cout));
		#endif

	}

	#ifdef TRACE_ON
		verilatorWaveformTracer->flush();
		verilatorWaveformTracer->close();
	#endif

	cout << "--------------------------------------------------------------\n";
	cout << "   Simulation Completed\n";

	logFile.close();
	sigFile.close();
	delete tb;
	exit(EXIT_SUCCESS);

}
