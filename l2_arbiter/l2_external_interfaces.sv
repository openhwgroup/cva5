/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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
    //l2_request_t request;
    logic [29:0] addr;
    logic [3:0] be;
    logic rnw;
    logic is_amo;
    logic [4:0] amo_type_or_burst_size;
    logic [L2_SUB_ID_W-1:0] sub_id;

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

    modport master (output addr, be, rnw, is_amo, amo_type_or_burst_size, sub_id,
            output request_push, input request_full,
            input inv_addr, inv_valid, output  inv_ack,
            input con_result, con_valid,
            output wr_data, wr_data_push, input data_full,
            input rd_data, rd_sub_id, rd_data_valid, output rd_data_ack);

    modport slave (input addr, be, rnw, is_amo, amo_type_or_burst_size, sub_id,
            input request_push, output request_full,
            output inv_addr, inv_valid, input  inv_ack,
            output con_result, con_valid,
            input wr_data, wr_data_push, output data_full,
            output rd_data, rd_sub_id, rd_data_valid, input rd_data_ack);
endinterface


interface l2_memory_interface #( parameter L2_ID_W = $clog2(L2_NUM_PORTS) + L2_SUB_ID_W);
    logic [29:0] addr;
    logic [3:0] be;
    logic rnw;
    logic is_amo;
    logic [4:0] amo_type_or_burst_size;
    logic [L2_ID_W-1:0] id;

    logic request_pop;
    logic request_valid;

    logic abort;

    logic [31:0] wr_data;
    logic wr_data_valid;
    logic wr_data_read;

    logic [31:0] rd_data;
    logic  [L2_ID_W-1:0] rd_id;
    logic rd_data_valid;

    modport master (output addr, be, rnw, is_amo, amo_type_or_burst_size, id,
            output request_valid, abort, input request_pop,
            output wr_data, wr_data_valid, input wr_data_read,
            input rd_data, rd_id, rd_data_valid);

    modport slave (input addr, be, rnw, is_amo, amo_type_or_burst_size, id,
            input request_valid, abort, output request_pop,
            input wr_data, wr_data_valid, output wr_data_read,
            output rd_data, rd_id, rd_data_valid);
endinterface

