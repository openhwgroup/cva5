/*
 * Copyright © 2017, 2019 Eric Matthews,  Lesley Shannon
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

import l2_config_and_types::*;

interface l2_requester_interface;
    l2_request_t request;
    logic request_push;
    logic request_full;

    logic [31:2] inv_addr;
    logic inv_valid;
    logic inv_ack;

    logic con_result;
    logic con_valid;

    logic [31:0] wr_data;
    logic wr_data_push;
    logic data_full;

    logic [31:0] rd_data;
    logic [L2_SUB_ID_W-1:0] rd_sub_id;
    logic rd_data_valid;
    logic rd_data_ack;

    modport master (output request, request_push, input request_full,
            input inv_addr, inv_valid, output  inv_ack,
            input con_result, con_valid,
            output wr_data, wr_data_push, input data_full,
            input rd_data, rd_sub_id, rd_data_valid, output rd_data_ack);

    modport slave (input request, request_push, output request_full,
            output inv_addr, inv_valid, input  inv_ack,
            output con_result, con_valid,
            input wr_data, wr_data_push, output data_full,
            output rd_data, rd_sub_id, rd_data_valid, input rd_data_ack);
endinterface


interface l2_memory_interface;
    l2_mem_request_t request;
    logic request_pop;
    logic request_valid;

    logic abort;

    logic [31:0] wr_data;
    logic wr_data_valid;
    logic wr_data_read;

    logic [31:0] rd_data;
    logic  [L2_ID_W-1:0] rd_id;
    logic rd_data_valid;

    modport master (output request, request_valid, abort, input request_pop,
            output wr_data, wr_data_valid, input wr_data_read,
            input rd_data, rd_id, rd_data_valid);

    modport slave (input request, request_valid, abort, output request_pop,
            input wr_data, wr_data_valid, output wr_data_read,
            output rd_data, rd_id, rd_data_valid);
endinterface


interface l2_fifo_interface #(parameter DATA_WIDTH = 32);
    logic push;
    logic pop;
    logic [DATA_WIDTH-1:0] data_in;
    logic [DATA_WIDTH-1:0] data_out;
    logic valid;
    logic full;
    logic empty;
    modport enqueue (input full, empty, output data_in, push);
    modport dequeue (input valid, data_out, output pop);
    modport structure(input push, pop, data_in, output data_out, valid, full, empty);
endinterface

interface l2_arbitration_interface;
    logic [L2_NUM_PORTS-1:0] requests;
    logic [$clog2(L2_NUM_PORTS)-1:0] grantee_i;
    logic [L2_NUM_PORTS-1:0] grantee_v;
    logic grantee_valid;
    logic strobe;

    modport slave (input requests, strobe, output grantee_i, grantee_v , grantee_valid);
    modport master (output requests, strobe, input grantee_i, grantee_v , grantee_valid);
endinterface
