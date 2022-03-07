/*
 * Copyright © 2019 Eric Matthews,Zavier Aguila  Lesley Shannon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 *			   Zavier Aguila <zaguila@sfu.ca>
 */

#ifndef AXIDDR_H
#define AXIDDR_H
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <cmath>
#include <map>
#include <random>
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vcva5_sim.h"
#include "axi_interface.h"
#include "ddr_page.h"

using namespace std;


struct addr_calculation_parameters{
	uint32_t address;
	uint32_t increment;
	uint32_t wrap_boundary;
    int number_bytes; 
    int burst_length; 
	int number_of_bursts_left;
	int delay_cycles_left;
};

 class axi_ddr_sim{
 	public:
	//Functions--------------------------------------------------------------
	//Init instructions-----------------
 	axi_ddr_sim();
	//Initialize DDR
 	axi_ddr_sim(Vcva5_sim * tb);

	//Initialize DDR from file
 	axi_ddr_sim(string filepath, uint32_t starting_memory_location, int number_of_bytes, Vcva5_sim * tb);
 	axi_ddr_sim(ifstream & input_memory_file, Vcva5_sim * tb);
 	void step();
 	int get_data(uint32_t data_address);

 	ddr_page get_page(uint32_t page_address);
 	
 	void set_data(uint32_t data_address, uint32_t set_data, uint32_t byte_enable);

 	//Queue Handling Functions-------------------------------------


	//AXI Functions-------------------------------------
	//Latency Randomizer
	//Byte Enable Handler
	//Burst Handler

	//Base AXI Read Reply
	//BASE AXI Write Reply
	private:
		default_random_engine generator;
		uniform_int_distribution<int> read_distribution;
		uniform_int_distribution<int> write_distribution;
		//Pointers to Data
		map<uint32_t,ddr_page> ddr_pages;
		Vcva5_sim *tb;
 		void parse_output_signals();

 		void parse_input_signals();
		void update_current_read_parameters();
		void update_current_write_parameters();
		void handle_write_req();
 		void handle_read_req();
 		void init_signals();

 		addr_calculation_parameters current_read_parameters{0,0,0,0};
 		addr_calculation_parameters current_write_parameters{0,0,0,0};
		//Read Request Queue
		queue<AXI_read_address_channel_signals> rd_ad_channel_queue;
		//Write Request Queue
		queue<AXI_write_address_channel_signals> wr_ad_channel_queue;
		//Read Data Queue
		queue<AXI_read_data_channel_signals> r_data_channel_queue;
		//Write Data Queue
		queue<AXI_write_data_channel_signals> w_data_channel_queue;
		//Write Response Queue
		queue<AXI_write_response_channel_signals> w_res_channel_queue;

		unsigned starting_location = 0x80000000;
};

#endif