#include "axi_ddr_sim.h"
#include "ddr_page.h"
#include <stdint.h>
#include <iostream>
#include <cstdlib>
#include <assert.h>
using namespace	 std;

template <class TB>
axi_ddr_sim<TB>::axi_ddr_sim(TB * tb){
    this->tb = tb;
}
template <class TB>
void axi_ddr_sim<TB>::init_signals(){
    tb->ddr_axi_bresp = 0;
    tb->ddr_axi_bvalid = 0;
    tb->ddr_axi_rvalid = 0;
    tb->ddr_axi_rdata = 0;
    tb->ddr_axi_rid = 0;
    tb->ddr_axi_rlast = 0;
    tb->ddr_axi_rresp = 0;
    tb->ddr_axi_rvalid = 0;
}

template <class TB>
axi_ddr_sim<TB>::axi_ddr_sim(string filepath, uint32_t starting_memory_location, int number_of_bytes, TB * tb){
    ifstream input_memory_file;
    input_memory_file.open(filepath);
    string line;


    uint32_t max_pages = starting_memory_location/PAGE_SIZE + number_of_bytes/PAGE_SIZE;
    //Parse the uniform pages
    uint32_t page_index = starting_memory_location/PAGE_SIZE;
    for (; page_index < max_pages; page_index++){
     ddr_page page;
        for(int data_index = 0; data_index < PAGE_SIZE/4; data_index++){
            getline(input_memory_file, line);
            //Read 32-bit number represented through hexidecimals
            page.write_data(data_index, stoul(line, 0, 16));
        }
        ddr_pages.insert(pair<uint32_t,ddr_page>((uint32_t)(page_index*PAGE_SIZE), page));
    }
       generator = default_random_engine(DELAY_SEED);
       read_distribution = uniform_int_distribution<int>(MIN_DELAY_RD,MAX_DELAY_RD);
       write_distribution = uniform_int_distribution<int>(MIN_DELAY_WR,MAX_DELAY_WR);
    this->tb = tb;
    init_signals();
    //printf("Done AXI Initialization. %d Pages intialized\n", page_index);
    fflush(stdout);
}


template <class TB>
axi_ddr_sim<TB>::axi_ddr_sim(ifstream & input_memory_file, TB * tb){
    string line;

    uint32_t max_pages = DDR_SIZE/PAGE_SIZE;
    //Parse the uniform pages
    bool not_finished = true;
    uint32_t page_index = starting_location/PAGE_SIZE;
    for (; page_index < max_pages; page_index++){
     ddr_page page;

        for(int data_index = 0; data_index < PAGE_SIZE/4; data_index++){
            not_finished = (bool)getline(input_memory_file, line);
            if(!not_finished)
                break;
            //Read 32-bit number represented through hexidecimals
            page.write_data(data_index, stoul(line, 0, 16));
        }
        if(!not_finished)
            break;
        ddr_pages.insert(pair<uint32_t,ddr_page>((uint32_t)(page_index*PAGE_SIZE), page));
        fflush(stdout);
    }

       generator = default_random_engine(DELAY_SEED);
       read_distribution = uniform_int_distribution<int>(MIN_DELAY_RD,MAX_DELAY_RD);
       write_distribution = uniform_int_distribution<int>(MIN_DELAY_WR,MAX_DELAY_WR);
    this->tb = tb;
    init_signals();
    //printf("Done AXI Initialization. Started from: %u\n", starting_location);
    fflush(stdout);
}

template <class TB>
int axi_ddr_sim<TB>::get_data(uint32_t data_address){
    uint32_t starting_address = (data_address / PAGE_SIZE) * PAGE_SIZE;
    if(ddr_pages.count(starting_address)){ //If page exists
        return ddr_pages[starting_address].return_data(data_address%PAGE_SIZE/4);
    }
    else{//If it doesn't, instantiate a new page
        ddr_page page;
        ddr_pages.insert(pair<uint32_t,ddr_page>(starting_address, page));
        assert(ddr_pages.count(starting_address)); //Check if it was intialized
        return ddr_pages[starting_address].return_data(data_address%PAGE_SIZE/4);
    }
}
template <class TB>
void  axi_ddr_sim<TB>::set_data(uint32_t data_address, uint32_t set_data, uint32_t byte_enable){
    uint32_t data = get_data(data_address);
    uint32_t starting_address = (data_address / PAGE_SIZE) * PAGE_SIZE;
    data = (data & ~byte_enable) | (set_data & byte_enable);
    ddr_pages[starting_address].write_data(data_address%PAGE_SIZE/4, data);

};

template <class TB>
ddr_page axi_ddr_sim<TB>::get_page(uint32_t page_address){
    return ddr_pages[page_address];
}
template <class TB>
void axi_ddr_sim<TB>::parse_input_signals(){
    //If the master has a write requests
    if(tb->ddr_axi_awvalid && wd_ad_channel_queue.size() < MAX_INFLIGHT_WD_REQ){
        AXI_write_address_channel_signals elem{tb->ddr_axi_awaddr, tb->ddr_axi_awlen, tb->ddr_axi_awsize, tb->ddr_axi_awburst,tb->ddr_axi_awcache,tb->ddr_axi_awid};
        wd_ad_channel_queue.push(elem);
    }
    //If the master has write data
    if(tb->ddr_axi_wvalid){
        AXI_write_data_channel_signals elem{tb->ddr_axi_wid, tb->ddr_axi_wdata, tb->ddr_axi_wstrb, tb->ddr_axi_wlast};
        w_data_channel_queue.push(elem);
    }
    //If the master has a read request
     if(tb->ddr_axi_arvalid && rd_ad_channel_queue.size() < MAX_INFLIGHT_RD_REQ){
        AXI_read_address_channel_signals elem{tb->ddr_axi_araddr, tb->ddr_axi_arlen, tb->ddr_axi_arsize, tb->ddr_axi_arburst, tb->ddr_axi_arcache, tb->ddr_axi_arid};
        rd_ad_channel_queue.push(elem);
     }
}
template <class TB>
void axi_ddr_sim<TB>::parse_output_signals(){
    if(tb->rst ==1){
        tb->ddr_axi_wready = 0;
        tb->ddr_axi_arready = 0;
        
        tb->ddr_axi_bid = 0;
        tb->ddr_axi_bresp = 0;
        tb->ddr_axi_bvalid = 0;
        tb->ddr_axi_rid = 0;
        tb->ddr_axi_rdata = 0;
        tb->ddr_axi_rresp = 0;
        tb->ddr_axi_rlast = 0;
        //tb->ddr_axi_ruser = 0;
        tb->ddr_axi_rvalid = 0;

    }
    else { 
    tb->ddr_axi_wready = 1;

    //Write Req
    if(wd_ad_channel_queue.size() < MAX_INFLIGHT_WD_REQ)
        tb->ddr_axi_awready = 1;
    else
        tb->ddr_axi_awready = 0;
    
    //Read Req
    if(rd_ad_channel_queue.size() < MAX_INFLIGHT_RD_REQ)
        tb->ddr_axi_arready = 1;
    else
        tb->ddr_axi_arready = 0;

    //If we the write_response
    if(w_res_channel_queue.size() > 0){
        AXI_write_response_channel_signals elem = w_res_channel_queue.front();
        if(tb->ddr_axi_bready)
            w_res_channel_queue.pop();
        
        tb->ddr_axi_bid = elem.bid;
        tb->ddr_axi_bresp = elem.bresp;
        tb->ddr_axi_bvalid = 1;
    }
    else{
        tb->ddr_axi_bid = rand();
        tb->ddr_axi_bresp = rand();
        //tb->ddr_axi_buser = rand();
        tb->ddr_axi_bvalid = 0;
    }

    //If we have the read data
    if(r_data_channel_queue.size() > 0){
        AXI_read_data_channel_signals elem = r_data_channel_queue.front();
        if(tb->ddr_axi_rready){
            //cout << "Before: " << r_data_channel_queue.size() << endl;
            r_data_channel_queue.pop();
            //cout << "After: " << r_data_channel_queue.size() << endl;
        }
        tb->ddr_axi_rid = elem.rid;
        tb->ddr_axi_rdata = elem.rdata;
        tb->ddr_axi_rresp = elem.rresp;
        tb->ddr_axi_rlast = elem.rlast;
        //tb->ddr_axi_ruser = elem.ruser;
        tb->ddr_axi_rvalid = 1;
    }
    else{
        tb->ddr_axi_rid = rand();
        tb->ddr_axi_rdata = rand();
        tb->ddr_axi_rresp = rand();
        tb->ddr_axi_rlast = 0;
        //tb->ddr_axi_ruser = rand();
        tb->ddr_axi_rvalid = 0;
    }
    }
}
template <class TB>
void axi_ddr_sim<TB>::handle_read_req(){
    if(rd_ad_channel_queue.size() > 0 ){
        if(current_read_parameters.delay_cycles_left == 0){
            AXI_read_data_channel_signals elem;
            elem.rid = rd_ad_channel_queue.front().arid;
            elem.rdata =  get_data(current_read_parameters.address);
            current_read_parameters.number_of_bursts_left--;

            if(rd_ad_channel_queue.front().arburst == 0 ){//FIXED
                //do nothing
            }
            else if(rd_ad_channel_queue.front().arburst == 1){ //INCR
                //Increment Address by number of bytes in a burst(arsize)
                current_read_parameters.address += current_read_parameters.increment;

            }
            else if(rd_ad_channel_queue.front().arburst == 2){ //WRAP
                current_read_parameters.address += current_read_parameters.increment;
                if(current_read_parameters.address == current_read_parameters.wrap_boundary + current_read_parameters.number_bytes * current_read_parameters.burst_length){
                    current_read_parameters.address = current_read_parameters.wrap_boundary;
                }
            }
            elem.rresp = 0; //OKAY bx00
            //elem.ruser = rd_ad_channel_queue.front().aruser;
            if(current_read_parameters.number_of_bursts_left == 0){
                elem.rlast = 1;
                rd_ad_channel_queue.pop();
            }
            else
                elem.rlast = 0;
            r_data_channel_queue.push(elem);
        }
        else{
            current_read_parameters.delay_cycles_left--;
        }
    }

}
template <class TB>
void axi_ddr_sim<TB>::handle_write_req(){
    //cout << "w_data_channel_queue size: " << w_data_channel_queue.size() << endl;
    //cout << "current_write_parameters.number_of_bursts_left: " << current_write_parameters.number_of_bursts_left << endl;
    if(w_data_channel_queue.size() > 0 && current_write_parameters.number_of_bursts_left > 0){
            if(current_write_parameters.delay_cycles_left == 0){
            AXI_write_data_channel_signals elem = w_data_channel_queue.front();
            w_data_channel_queue.pop();
            //Calculate Byte Enable
            uint32_t byte_enable = 0;
            if(elem.wstrb >= 8){
                byte_enable = byte_enable | 0xFF000000;
                elem.wstrb -= 8;
            }
            if(elem.wstrb >= 4){
                byte_enable = byte_enable | 0x00FF0000;
                elem.wstrb -= 4;
            }
            if(elem.wstrb >= 2){
                byte_enable = byte_enable | 0x0000FF00;
                elem.wstrb -= 2;
            }
            if(elem.wstrb == 1){
                byte_enable = byte_enable | 0x000000FF;
                elem.wstrb -= 1;
            }
            set_data(current_write_parameters.address, elem.wdata, byte_enable);
            current_write_parameters.number_of_bursts_left--;

            if(wd_ad_channel_queue.front().awburst == 0 ){//FIXED
                //do nothing
            }
            else if(wd_ad_channel_queue.front().awburst == 1){ //INCR
                //Increment Address by number of bytes in a burst(arsize)
                current_write_parameters.address += current_write_parameters.increment;

            }
            else if(wd_ad_channel_queue.front().awburst == 2){ //WRAP
                current_write_parameters.address += current_write_parameters.increment;
                if(current_write_parameters.address == current_write_parameters.wrap_boundary + current_write_parameters.number_bytes * current_write_parameters.burst_length){
                    current_write_parameters.address = current_write_parameters.wrap_boundary;
                }
            }
            //If the Write is done
            if(current_write_parameters.number_of_bursts_left == 0){
                AXI_write_response_channel_signals resp_elem;
                resp_elem.bid = elem.wid;
                resp_elem.bresp = 0;
                wd_ad_channel_queue.pop();
                w_res_channel_queue.push(resp_elem);
            }
        }
        else{
            current_write_parameters.delay_cycles_left--;
        }
    }
}

template <class TB>
void axi_ddr_sim<TB>::update_current_read_parameters(){
    //If I can serve a new read request
    if(rd_ad_channel_queue.size() > 0 && current_read_parameters.number_of_bursts_left == 0){
        current_read_parameters.address = rd_ad_channel_queue.front().araddr;
        current_read_parameters.number_of_bursts_left = rd_ad_channel_queue.front().arlen +1;
        current_read_parameters.delay_cycles_left = read_distribution(generator);
        if(rd_ad_channel_queue.front().arburst == 0 ){//FIXED
            current_read_parameters.increment = 0;
        }
        else if(rd_ad_channel_queue.front().arburst == 1){ //INCR
            //Increment Address by number of bytes in a burst(arsize)
            current_read_parameters.increment = pow(2,rd_ad_channel_queue.front().arsize);

        }
        else if(rd_ad_channel_queue.front().arburst == 2){ //WRAP
            current_read_parameters.increment = pow(2,rd_ad_channel_queue.front().arsize);
            current_read_parameters.number_bytes = pow(2,rd_ad_channel_queue.front().arsize);
            current_read_parameters.burst_length = rd_ad_channel_queue.front().arlen +1;
            current_read_parameters.wrap_boundary =  (int)(current_read_parameters.address/(current_read_parameters.number_bytes * current_read_parameters.burst_length)) * (current_read_parameters.number_bytes * current_read_parameters.burst_length);
        }
    }
}
template <class TB>
void axi_ddr_sim<TB>::update_current_write_parameters(){
    //If I can serve a new read request
    if(wd_ad_channel_queue.size() > 0 && current_write_parameters.number_of_bursts_left == 0){
        current_write_parameters.address = wd_ad_channel_queue.front().awaddr;
        current_write_parameters.number_of_bursts_left = wd_ad_channel_queue.front().awlen +1;
        current_write_parameters.delay_cycles_left = write_distribution(generator);
        if(wd_ad_channel_queue.front().awburst == 0 ){//FIXED
            current_write_parameters.increment = 0;
        }
        else if(wd_ad_channel_queue.front().awburst == 1){ //INCR
            //Increment Address by number of bytes in a burst(arsize)
            current_write_parameters.increment = pow(2,wd_ad_channel_queue.front().awsize);

        }
        else if(wd_ad_channel_queue.front().awburst == 2){ //WRAP
            current_write_parameters.increment = pow(2,wd_ad_channel_queue.front().awsize);
            current_write_parameters.number_bytes = pow(2,wd_ad_channel_queue.front().awsize);
            current_write_parameters.burst_length = wd_ad_channel_queue.front().awlen +1;
            current_write_parameters.wrap_boundary =  (int)(current_write_parameters.address/(current_write_parameters.number_bytes * current_write_parameters.burst_length)) * (current_write_parameters.number_bytes * current_write_parameters.burst_length);
        }
    }
}

template <class TB>
void axi_ddr_sim<TB>::step(){

    parse_input_signals();
    update_current_read_parameters();
    update_current_write_parameters();
    handle_read_req();
    handle_write_req();
    parse_output_signals();
}