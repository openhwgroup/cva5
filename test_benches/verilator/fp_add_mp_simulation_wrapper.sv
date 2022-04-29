import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module fp_add_mp_simulation_wrapper (
  input clk,
  input rst,
  //inputs
  input logic [FPLEN-1:0]    rs1,
  input logic [FPLEN-1:0]    rs2,
  input logic [6:0]         fn7,
  input logic [2:0]         rm,
  //issue
  input logic possible_issue,
  input logic new_request,
  input logic new_request_r,
  input fp_instruction_id_t instruction_id,
  output logic ready,
  //writeback
  output fp_instruction_id_t id,
  output logic done,
  output logic [FPLEN-1:0] rd,
  //fcsr
  output [4:0] fflags
  );

  fp_add_inputs_t fp_add_inputs;
  fp_unit_issue_interface issue();
  fp_unit_writeback_t fp_wb; 

  fp_add_mp #(.FRAC_W(FRAC_W), .EXPO_W(EXPO_W)) fp_add (
                .clk          (clk),
                .rst          (rst),
                .fp_add_inputs(fp_add_inputs),
                .rs1_grs      (3'b0),
                .issue        (issue),
                .fp_wb        (fp_wb),
                .fflags       (fflags)
                );


  //always_ff @ (posedge clk) begin 
    //fp_add_inputs.rs1 <= rs1;
    //fp_add_inputs.rs2 <= rs2;
    //fp_add_inputs.fn7 <= fn7;
    //fp_add_inputs.rm <= rm;

    //ready <= issue.ready;
    //issue.possible_issue <= possible_issue;
    //issue.new_request <= new_request;
    //issue.new_request_r <= new_request_r;
    //issue.instruction_id <= instruction_id;
  //end

  assign fp_add_inputs.rs1 = rs1;
  assign fp_add_inputs.rs2 = rs2;
  assign fp_add_inputs.fn7 = fn7;
  assign fp_add_inputs.rm = rm;

  assign ready = issue.ready;
  assign issue.possible_issue = possible_issue;
  assign issue.new_request = new_request;
  assign issue.new_request_r = new_request_r;
  assign issue.instruction_id = instruction_id;

  assign id = fp_wb.id;
  assign done = fp_wb.done;
  assign rd = fp_wb.rd;
endmodule
