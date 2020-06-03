#ifndef DDR_PAGEH
#define DDR_PAGEH
#include <stdint.h>

class ddr_page{
	public:
		ddr_page();
		uint32_t return_data(int data_address);
		void write_data(int data_address, int data);
	private:
		uint32_t data[PAGE_SIZE/4];
};
#endif