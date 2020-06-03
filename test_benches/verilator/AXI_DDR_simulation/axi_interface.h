#ifndef AXIINTERFACE_H
#define AXIINTERFACE_H
#include <stdint.h>

using namespace std;
struct AXI_write_address_channel_signals{
    uint32_t awaddr;
    uint32_t awlen;
    uint32_t awsize;
    uint32_t awburst;
    uint32_t awcache;
    uint32_t awid;
    //uint32_t awready;
};
struct AXI_read_address_channel_signals{

    uint32_t araddr;
    uint32_t arlen;
    uint32_t arsize;
    uint32_t arburst;
    uint32_t arcache;
    uint32_t arid;

};
struct AXI_write_data_channel_signals{
	uint32_t wid;
	uint32_t wdata;
	uint32_t wstrb;
	uint32_t wlast;
	//uint32_t wuser;
	//uint32_t wvalid;
	//uint32_t wready;
};
struct AXI_write_response_channel_signals{
	uint32_t bid;
	uint32_t bresp;
	//uint32_t buser;
	uint32_t bvalid;
	//uint32_t bready;
};
struct AXI_read_data_channel_signals{
	uint32_t rid;
	uint32_t rdata;
	uint32_t rresp;
	uint32_t rlast;
	//uint32_t ruser;
	//uint32_t rvalid;
	//uint32_t rready;
};


struct AXI_channels{
	AXI_read_address_channel_signals rd_ad_channel;
	AXI_write_address_channel_signals wd_ad_channel;
	AXI_read_data_channel_signals r_data_channel;
	AXI_write_data_channel_signals w_data_channel;
	AXI_write_response_channel_signals w_res_channel;
};
#endif