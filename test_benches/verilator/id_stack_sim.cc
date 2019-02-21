#include <stdlib.h>
#include <iostream>
#include <random>

#include "Vid_stack.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

using namespace std;

int stack_occupancy_count;

bool id_check(Vid_stack *tb) {
	bool result = true;
	for (int i = 0; i < 4; i++) {
		for (int j = i + 1; j < 4; j++) {
			result = result && (tb->ordering[i] != tb->ordering[j]);
		}
	}
	return result;
}

bool inuse[4];

//Only retire IDs that have been issued (or true if none issued)
bool retired_id_valid(Vid_stack *tb) {
	return (stack_occupancy_count == 0) || inuse[tb->retired_id];
}

std::mt19937 rng;
std::bernoulli_distribution dist(0.5);

void generate_random_valid_inputs(Vid_stack *tb) {
	int occupancy_change;

	do {
		occupancy_change = 0;
		tb->issued = dist(rng);
		tb->retired = dist(rng);
		tb->retired_id = (dist(rng) << 1) | dist(rng);
		occupancy_change += tb->issued;
		occupancy_change -= tb->retired;
	} while (
			(tb->retired && stack_occupancy_count == 0) ||
			(tb->issued && tb->retired && stack_occupancy_count == 4) ||
			(stack_occupancy_count + occupancy_change) < 0 || (stack_occupancy_count + occupancy_change) > 4
		    || !retired_id_valid(tb));

	if (tb->retired)
		inuse[tb->retired_id] = false;

	if (tb->issued)
		inuse[tb->ordering[3-stack_occupancy_count]] = true;

	int id_index = 0;

	for(int i=0; i < 4; i++) {
		if (tb->retired_id == tb->ordering[i])
			id_index = i;
	}

	tb->shift_bits = (1 << (id_index + 1)) - 1;

	stack_occupancy_count += occupancy_change;

	cout << "gen: "<< (int)(tb->issued) << " " << (int)(tb->retired) << " " << (int)(tb->retired_id) <<  " " << stack_occupancy_count;
	cout << " [";
	for(int i=0; i < 4; i++)
		cout << inuse[i] << " ";
	cout << "]" << "\n";

}

int main(int argc, char **argv) {
	// Initialize Verilators variables
	Verilated::commandArgs(argc, argv);
	Verilated::traceEverOn(true);

	// Create an instance of our module under test
	Vid_stack *tb = new Vid_stack;
	VerilatedVcdC *tracer = new VerilatedVcdC;

	tb->trace(tracer, 99);
	tracer->open("id_stack_sim_results.vcd");

	cout << "Starting test\n";
	cout << "******************************\n";
	int reset_count = 0;
	long int cycle_cout = 0;
	stack_occupancy_count = 0;
	tb->rst = 1;
	tb->issued = 0;
	tb->retired = 0;
	tb->retired_id = 0;
	tb->clk = 0;
	tb->shift_bits = 0;

	for(int i=0; i < 4; i++)
		inuse[i] = false;

	// Tick the clock until we are done
	while (!Verilated::gotFinish()) {
		if (reset_count > 64) {
			tb->rst = 0;
		} else {
			reset_count++;
		}

		if (cycle_cout >= 1000) {
			break;
		}

		tb->clk = 0;
		tb->eval();
		tb->clk = 1;
		tb->eval();


		if (tb->rst == 0)
			generate_random_valid_inputs(tb);

		tracer->dump(vluint64_t(cycle_cout));
		cycle_cout++;
	}
	tracer->flush();
	tracer->close();
	cout << "******************************\n";
	cout << "Test Done\n";
	cout << "Simulated: " << cycle_cout << " cycles.";

	delete tb;
	exit (EXIT_SUCCESS);

}
