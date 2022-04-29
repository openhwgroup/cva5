import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module fp_div_sqrt_simulation_wrapper(
    input logic clk,
    input logic rst,
    input logic [FLEN-1:0] rs1,
    input logic [FLEN-1:0] rs2,
    input logic [2:0] rm,
    input logic [6:0] fn7,
    id_t instruction_id,

    input logic new_request,
    input logic possible_issue,
    output logic ready,

    output logic [FLEN-1:0] rd,
    output logic done,
    input logic ack
);

    unit_issue_interface issue();
    fp_unit_writeback_interface wb();
    fp_div_sqrt_inputs_t fp_div_sqrt_inputs;

    assign issue.new_request = new_request;
    assign issue.id = instruction_id;
    assign ready = issue.ready;

    assign rd = fp_wb_packet[0].data;
    assign done = fp_wb_packet[0].valid;
    assign fp_unit_wb[FP_WB_IDS.FDIV_SQRT].ack = fp_unit_wb[FP_WB_IDS.FDIV_SQRT].done; //retire as soon as instructio is done

    assign fp_div_sqrt_inputs.fn7 = fn7;
    assign fp_div_sqrt_inputs.rs1 = rs1;
    assign fp_div_sqrt_inputs.rs1_special_case = {is_inf[RS1], is_SNaN[RS1], is_QNaN[RS1], is_zero[RS1]}; 
    assign fp_div_sqrt_inputs.rs2 = rs2;
    assign fp_div_sqrt_inputs.rs2_special_case = {is_inf[RS2], is_SNaN[RS2], is_QNaN[RS2], is_zero[RS2]};
    assign fp_div_sqrt_inputs.rm = rm;
    assign fp_div_sqrt_inputs.rs1_hidden_bit = hidden_bit[RS1];
    assign fp_div_sqrt_inputs.rs2_hidden_bit = hidden_bit[RS2];

    fp_div_sqrt_wrapper div_sqrt_inst(
      .clk(clk),
      .rst(rst),
      .fp_div_sqrt_inputs(fp_div_sqrt_inputs),
      .issue(issue),
      .wb(fp_unit_wb[FP_WB_IDS.FDIV_SQRT])
    );

    //writeback stuff
    localparam int unsigned FLS_WB_ID = 32'd0;
    localparam int unsigned FMADD_WB_ID = FLS_WB_ID + 1;
    localparam int unsigned FMUL_WB_ID = FMADD_WB_ID + 1;
    localparam int unsigned FDIV_SQRT_WB_ID = FMUL_WB_ID + 1;
    localparam int unsigned MISC_WB2FP_WB_ID = FDIV_SQRT_WB_ID + 1;

    localparam int unsigned FP_NUM_WB_UNITS = MISC_WB2FP_WB_ID + 1;
    localparam int unsigned FP_NUM_UNITS_PER_PORT [FP_NUM_WB_GROUPS] = '{FP_NUM_WB_UNITS};
    localparam fp_wb_id_param_t FP_WB_IDS = '{
          FLS       : FLS_WB_ID,
          FMADD     : FMADD_WB_ID,
          FMUL      : FMUL_WB_ID,
          FDIV_SQRT : FDIV_SQRT_WB_ID,
          MISC_WB2FP: MISC_WB2FP_WB_ID 
      };

    fp_unit_writeback_interface fp_unit_wb  [FP_NUM_WB_UNITS]();
    fflags_writeback_t fp_unit_fflag_wb_packet;
    fp_wb_packet_t fp_wb_packet [FP_NUM_WB_GROUPS];
    fp_wb_packet_t fp_wb_snoop;
    logic adder_path;
    logic add;
    logic rs1_hidden_bit;
    logic rs2_hidden_bit;
    logic is_inf[FP_REGFILE_READ_PORTS];
    logic is_SNaN[FP_REGFILE_READ_PORTS];
    logic is_QNaN[FP_REGFILE_READ_PORTS];
    logic is_zero[FP_REGFILE_READ_PORTS];
    logic hidden_bit[FP_REGFILE_READ_PORTS];

    fp_writeback #(
        .CONFIG (EXAMPLE_CONFIG),
        .NUM_UNITS (FP_NUM_UNITS_PER_PORT),
        .NUM_WB_UNITS (FP_NUM_WB_UNITS)
      )
      fp_writeback_block (
        .clk (clk),
        .rst (rst),
        .wb_packet (fp_wb_packet),
        .unit_wb (fp_unit_wb),
        .fflags_wb_packet (fp_unit_fflag_wb_packet),
        .wb_snoop (fp_wb_snoop)
      );
 
    localparam VARIABLE_EXPO_WIDTH = EXPO_WIDTH;
    localparam VARIABLE_FRAC_WIDTH = FRAC_WIDTH;
    fp_special_case_detection_sandboxed #(.SANDBOX_FRAC_W(VARIABLE_FRAC_WIDTH), .SANDBOX_EXPO_W(VARIABLE_EXPO_WIDTH))
        rs1_special_case_detection (
          .data_in (rs1),
          .is_inf (is_inf[RS1]),
          .is_SNaN (is_SNaN[RS1]),
          .is_QNaN (is_QNaN[RS1]),
          .is_zero (is_zero[RS1]),
          .hidden (hidden_bit[RS1])
        );  

    fp_special_case_detection_sandboxed #(.SANDBOX_FRAC_W(VARIABLE_FRAC_WIDTH), .SANDBOX_EXPO_W(VARIABLE_EXPO_WIDTH))
        rs2_special_case_detection (
          .data_in (rs2),
          .is_inf (is_inf[RS2]),
          .is_SNaN (is_SNaN[RS2]),
          .is_QNaN (is_QNaN[RS2]),
          .is_zero (is_zero[RS2]),
          .hidden (hidden_bit[RS2])
        );  
endmodule

