#include "ddr_page.h"

ddr_page::ddr_page(){
}
uint32_t ddr_page::return_data(int data_address){
	return data[data_address];
}
void ddr_page::write_data(int data_address, int data_input){
	data[data_address] = data_input;
}