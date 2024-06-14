//
// Copyright © 2020  Stuart Hoad,  Lesley Shannon
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Initial code developed under the supervision of Dr. Lesley Shannon,
// Reconfigurable Computing Lab, Simon Fraser University.
//
// Author(s):
//             Stuart Hoad <shoad@sfu.ca>
//

import cva5_config::*;
import cva5_types::*;

module cva5_formal_wrapper (

        input logic clk,
        input logic rst
        );

// top level signals 

        local_memory_interface 	instruction_bram();
        local_memory_interface 	data_bram();

        axi_interface 		    m_axi();
        avalon_interface 	    m_avalon();
        wishbone_interface 	    m_wishbone();
		
        trace_outputs_t 	    trace;
        l2_requester_interface 	l2_req_if();
        logic 			        timer_interrupt;
        logic 			        ext_interrupt;

// Instance of CVA5 core
        cva5 
        u_cva5_core (
        .clk 		        (clk),
        .rst 		        (rst),
        .instruction_bram   (instruction_bram.master),
        .data_bram	        (data_bram.master),
        .m_axi		        (m_axi.master),
        .m_avalon	        (m_avalon.master),
        .m_wishbone	        (m_wishbone.master),
        .tr		            (trace),
        .l2		            (l2_req_if.master),
        .timer_interrupt    (timer_interrupt),
        .interrupt	        (ext_interrupt)
	);

// Instance of CVA5 FBM
        cva5_fbm 
        u_cva5_fbm (
        .clk 		        (clk),
        .rst 		        (rst),
        .instruction_bram   (instruction_bram.formal),
        .data_bram	        (data_bram.formal),
        .m_axi		        (m_axi.formal),
        .m_avalon	        (m_avalon.formal),
        .m_wishbone	        (m_wishbone.formal),
        .tr		            (trace),
        .l2		            (l2_req_if.formal),
        .timer_interrupt    (timer_interrupt),
        .interrupt	        (ext_interrupt)
	);


endmodule
