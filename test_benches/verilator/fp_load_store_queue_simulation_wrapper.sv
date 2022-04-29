import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_load_store_queue_simulation_wrapper (
	input logic clk,
	input logic rst,
	input logic gc_fetch_flush,
	input logic [31:0] addr,
    input logic load,
    input logic store,
    input logic [3:0] be,
    input logic [2:0] fn3,
    input logic [31:0] data_in,
    input instruction_id_t id,
    input logic forwarded_store,
    input instruction_id_t data_id,
    input logic possible_issue,
    input logic new_issue,
    output logic ready,
    output instruction_id_t id_needed_by_store,
    output logic transaction_ready,
    input logic accepted,
    input logic is_fp,
    input logic [FLEN-1:0] fp_data_in,
    input fp_instruction_id_t fp_id,
    input fp_instruction_id_t fp_data_id,
    output fp_instruction_id_t fp_id_needed_by_store,
    //transaction out 
	output logic [31:0] to_addr,
    output logic to_load,
    output logic to_store,
    output logic [3:0] to_be,
    output logic [2:0] to_fn3,
    output logic [31:0] to_data_in,
    output instruction_id_t to_id,
    output logic to_is_fp,
    output logic [FLEN-1:0] to_fp_data_in,
    output fp_instruction_id_t to_fp_id,

	output logic [MAX_INFLIGHT_COUNT-1:0] wb_hold_for_store_ids,
    //Writeback data
    input logic [31:0] writeback_data,
    input logic writeback_valid,

    //Gao - FPU support
    output logic [FP_MAX_INFLIGHT_COUNT-1:0] fp_wb_hold_for_store_ids,
    input logic [FLEN-1:0] fp_writeback_data,
    input logic fp_writeback_valid
	);
	
	load_store_queue_interface lsq();
	assign lsq.addr = addr; 
	assign lsq.load = load; 
	assign lsq.store = store; 
	assign lsq.be = be; 
	assign lsq.fn3 = fn3; 
	assign lsq.data_in = data_in; 
	assign lsq.id = id; 
	assign lsq.forwarded_store = forwarded_store;
	assign lsq.data_id = data_id;
	assign lsq.possible_issue = possible_issue;
	assign lsq.new_issue = new_issue;
	assign lsq.accepted = accepted;
	assign lsq.is_fp = is_fp;
	assign lsq.fp_id = fp_id; 
	assign lsq.fp_data_id = fp_data_id; 
	assign lsq.fp_data_in = fp_data_in;
	assign ready = lsq.ready; 
	assign id_needed_by_store = lsq.id_needed_by_store;
	assign fp_id_needed_by_store = lsq.fp_id_needed_by_store;
	// assign transaction_out = lsp.transaction_out;
	assign transaction_ready = lsq.transaction_ready;
	assign lsq.transaction_out = transaction_out;

	data_access_shared_inputs_t transaction_out;
	assign to_addr = transaction_out.addr;
	assign to_load = transaction_out.load;
	assign to_store = transaction_out.store;
	assign to_be = transaction_out.be;
	assign to_fn3 = transaction_out.fn3;
	assign to_data_in = transaction_out.data_in;
	assign to_id = transaction_out.id;
	assign to_is_fp = transaction_out.is_fp;
	assign to_fp_data_in = transaction_out.fp_data_in;
	assign to_fp_id = transaction_out.fp_id;
	
	fp_load_store_queue dut(.*);

endmodule : fp_load_store_queue_simulation_wrapper