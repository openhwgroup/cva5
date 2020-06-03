#include "axi_ddr_sim.h"
#include <iostream>
#include <iomanip>
#include <fstream>
using namespace std;


void DDR_file_init(string filename,int num_entries){
	ofstream init_file;
	init_file.open(filename);
		for (int i = 0; i < num_entries; i++ ){
		init_file << setfill('0') <<  setw(8) << hex << i << endl;
	}
};
int print_DDR_init(string filepath,uint32_t starting_memory_location, int number_of_bytes){
	axi_ddr_sim  AXI_DDR(filepath, starting_memory_location, number_of_bytes);

	ifstream input_memory_file;
	input_memory_file.open(filepath);
    string line;
	for(int data_index = starting_memory_location; data_index < int(starting_memory_location + number_of_bytes); data_index+=4){
    	cout << "[" << data_index << "]: " << AXI_DDR.get_data(data_index) << endl;

    }
    cout << "Starting Location: " << starting_memory_location << endl;
    cout << "Final value should be: " << number_of_bytes/4 - 1 << endl;
	return 0;
};

int main(){
	int num_entries = PAGE_SIZE * 5;
	uint32_t starting_location = PAGE_SIZE*0;
	DDR_file_init("DDR_init.txt",num_entries);
	print_DDR_init("DDR_init.txt", starting_location, num_entries*4);
	return 0;
}