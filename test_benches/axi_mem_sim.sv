/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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
 */

//No error checking for incorrect ordering of axi control signals from Master side of interface
import tb_tools::*;
import cva5_config::*;

module axi_mem_sim
        #(parameter string file_name = "")
        (
        input logic clk,
        input logic rst,
        axi_interface.slave axi,

        input logic[31:0] if_pc,
        input logic[31:0] dec_pc
        );

    typedef struct packed{
        logic [31:0] araddr;
        logic [7:0] arlen;
        logic [2:0] arsize;
        logic [1:0] arburst;
        logic [3:0] arcache;
        logic [5:0] arid;
    } read_request;

    typedef struct packed{
        logic [31:0] awaddr;
        logic [7:0] awlen;
        logic [2:0] awsize;
        logic [1:0] awburst;
        logic [3:0] awcache;
        logic [5:0] awid;
    } write_request;

    const int READ_QUEUE_DEPTH = 8;
    const int WRITE_QUEUE_DEPTH = 4;
    const int WRITE_DATA_QUEUE_DEPTH = 128;

    integer write_queue_size;
    integer read_data_queue_size;
    logic[47:0] write_request_count;
    logic[47:0] read_request_count;

    int read_burst_count;
    int processing_read_request;
    int processing_write_request;

    read_request read_queue[$];
    write_request write_queue[$];
    logic [31:0] write_data_queue[$];
    logic [31:0] read_data_queue[$];

    sim_mem ddr = new();

    //For opcode inspection
    string dec_opcode;
    string if_opcode;
    logic[0:64*8-1] if_inst_text;
    logic[0:64*8-1] dec_inst_text;
    /////////////////////

    function void getReadData (bit[31:0] addr, bit[7:0] len);
        for (int i = 0; i <= len; i=i+1) begin
            read_data_queue.push_back(ddr.readw(addr[31:2]+i));
        end
    endfunction

    //Simulation opcode support
    assign if_opcode = ddr.readopcode(if_pc[31:2]);
    assign dec_opcode = ddr.readopcode(dec_pc[31:2]);

    genvar i;
    generate
        for(i=0; i<64; i=i+1) begin
            always_comb begin
                if_inst_text[8*i: 8*(i+1) -1]=if_opcode[i];
                dec_inst_text[8*i: 8*(i+1) -1]=dec_opcode[i];
            end
        end
    endgenerate
    ///////////////////


    initial begin
        ddr.load_program(file_name, RESET_VEC);
    end

    //arready response
    assign axi.arready = read_queue.size() < READ_QUEUE_DEPTH;

    //Read request processing
    always_ff @(posedge clk) begin
        if (rst) begin
            read_request_count <= 0;
        end
        else if(axi.arvalid & axi.arready) begin
            read_queue.push_back(
                    {axi.araddr, axi.arlen, axi.arsize, axi.arburst, axi.arcache, axi.arid}
                );
            getReadData(axi.araddr, axi.arlen);
            read_request_count <=read_request_count+1;
        end
    end

    //Write request processing
    always_ff @(posedge clk) begin
        if(axi.awvalid & axi.awready) begin
            write_queue.push_back(
                    {axi.awaddr, axi.awlen, axi.awsize, axi.awburst, axi.awcache, axi.awid}
                );
        end
        write_queue_size <= write_queue.size();
    end
    assign axi.awready = write_queue.size() < WRITE_QUEUE_DEPTH;

    assign axi.wready = write_data_queue.size() < WRITE_DATA_QUEUE_DEPTH;

    //bresp
    always_ff @(posedge clk) begin
        if (rst) begin
            axi.bvalid <= 0;
        end
        else if(axi.wvalid & axi.wlast) begin
            axi.bresp <= 0;
            axi.bvalid <=1;
            axi.bid <= write_queue[0].awid;
            write_queue.pop_front();
        end
        else if (axi.bready) begin
            axi.bvalid <=0;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            write_request_count <= 0;
        end
        else if(axi.wvalid) begin
           write_request_count <= write_request_count + 1;
        end
    end

    //Handle write data
    always_ff @(posedge clk) begin
        if (rst) begin
        end
        else if(axi.wvalid) begin
            ddr.writew(write_queue.size > 0 ? write_queue[0].awaddr[31:2] : axi.awaddr[31:2], axi.wdata, axi.wstrb);
        end
    end

    always_ff @(posedge clk) begin
        read_data_queue_size <= read_data_queue.size();
    end

    //Return data
    always_ff @(posedge clk) begin
        if(rst) begin
            axi.rvalid <= 0;
            axi.rlast <= 0;
            read_burst_count <= 0;
        end
        else if(read_queue.size > 0) begin
            if(axi.rready) begin
                axi.rdata <= read_data_queue.pop_front();
                axi.rvalid <= 1;
                axi.rid <=  read_queue[0].arid;
                if( read_queue[0].arlen == read_burst_count) begin
                    axi.rlast <= 1;
                    read_queue.pop_front();
                    read_burst_count <= 0;
                end
                else begin
                    read_burst_count <= read_burst_count + 1;
                    axi.rlast <= 0;
                end
            end
            else begin
                axi.rvalid <= 0;
                axi.rlast <= 0;
            end
        end
        else begin
            axi.rvalid <= 0;
            axi.rlast <= 0;
        end
    end

endmodule


