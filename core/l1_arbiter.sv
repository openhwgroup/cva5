/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * This Source Code Form is "Incompatible With Secondary Licenses", as
 * defined by the Mozilla Public License, v. 2.0.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */
 
import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;

module l1_arbiter
        (
        input logic clk,
        input logic rst,

        l2_requester_interface.requester l2,

        output sc_complete,
        output sc_success,

        l1_arbiter_request_interface.arb l1_request[3:0],
        l1_arbiter_return_interface.arb l1_response[3:0]
        );

    l2_request_t[3:0] l2_requests;

    logic push_ready;

    assign l2.inv_ack = l1_response[L1_DCACHE_ID].inv_ack;
    assign l2.rd_data_ack = l2.rd_data_valid;
    assign sc_complete = l2.con_valid;
    assign sc_success = l2.con_result;

    //arbiter can pop address FIFO at a different rate than the data FIFO, so check that both have space.
    assign push_ready = ~l2.request_full & ~l2.data_full;


    assign l1_request[L1_DCACHE_ID].ack = l1_request[L1_DCACHE_ID].request & push_ready;
    assign l1_request[L1_DMMU_ID].ack = l1_request[L1_DMMU_ID].request & push_ready & ~l1_request[L1_DCACHE_ID].request;
    assign l1_request[L1_ICACHE_ID].ack = l1_request[L1_ICACHE_ID].request & push_ready & ~l1_request[L1_DCACHE_ID].request & ~l1_request[L1_DMMU_ID].request;
    assign l1_request[L1_IMMU_ID].ack = l1_request[L1_IMMU_ID].request & push_ready & ~l1_request[L1_DCACHE_ID].request & ~l1_request[L1_DMMU_ID].request & ~l1_request[L1_ICACHE_ID].request;

    assign l2.request_push = push_ready & (l1_request[L1_DCACHE_ID].request | l1_request[L1_DMMU_ID].request | l1_request[L1_ICACHE_ID].request | l1_request[L1_IMMU_ID].request);
    assign l2.wr_data_push = push_ready & l1_request[L1_DCACHE_ID].request & ~l1_request[L1_DCACHE_ID].rnw; //Assumes data cache has highest priority



    always_comb begin
        l2_requests[L1_DCACHE_ID].addr = l1_request[L1_DCACHE_ID].addr[31:2];
        l2_requests[L1_DCACHE_ID].rnw = l1_request[L1_DCACHE_ID].rnw;
        l2_requests[L1_DCACHE_ID].be = l1_request[L1_DCACHE_ID].be;
        l2_requests[L1_DCACHE_ID].is_amo = l1_request[L1_DCACHE_ID].is_amo;
        l2_requests[L1_DCACHE_ID].amo_type_or_burst_size = l1_request[L1_DCACHE_ID].is_amo ? l1_request[L1_DCACHE_ID].amo : l1_request[L1_DCACHE_ID].size;
        l2_requests[L1_DCACHE_ID].sub_id = L1_DCACHE_ID;
    end


  //  assign l2_requests[L1_DCACHE_ID] = l1_request[L1_DCACHE_ID].to_l2(L1_DCACHE_ID);
    assign l2_requests[L1_DMMU_ID] = l1_request[L1_DMMU_ID].to_l2(L1_DMMU_ID);
    assign l2_requests[L1_ICACHE_ID] = l1_request[L1_ICACHE_ID].to_l2(L1_ICACHE_ID);
    assign l2_requests[L1_IMMU_ID] = l1_request[L1_IMMU_ID].to_l2(L1_IMMU_ID);

    always_comb begin
        if (l1_request[L1_DCACHE_ID].request)
            l2.request = l2_requests[L1_DCACHE_ID];
        else if (l1_request[L1_DMMU_ID].request)
            l2.request = l2_requests[L1_DMMU_ID];
        else if (l1_request[L1_ICACHE_ID].request)
            l2.request = l2_requests[L1_ICACHE_ID];
        else
            l2.request = l2_requests[L1_IMMU_ID];
    end

    assign l2.wr_data = l1_request[L1_DCACHE_ID].data;

    assign l1_response[L1_DCACHE_ID].data = l2.rd_data;
    assign l1_response[L1_DMMU_ID].data = l2.rd_data;
    assign l1_response[L1_ICACHE_ID].data = l2.rd_data;
    assign l1_response[L1_IMMU_ID].data = l2.rd_data;

    assign l1_response[L1_DCACHE_ID].data_valid = l2.rd_data_valid && (l2.rd_sub_id == L1_DCACHE_ID);
    assign l1_response[L1_DMMU_ID].data_valid = l2.rd_data_valid && (l2.rd_sub_id == L1_DMMU_ID);
    assign l1_response[L1_ICACHE_ID].data_valid = l2.rd_data_valid && (l2.rd_sub_id == L1_ICACHE_ID);
    assign l1_response[L1_IMMU_ID].data_valid = l2.rd_data_valid && (l2.rd_sub_id == L1_IMMU_ID);

    assign l1_response[L1_DCACHE_ID].inv_addr = l2.inv_addr;
    assign l1_response[L1_DCACHE_ID].inv_valid = l2.inv_valid;


endmodule
