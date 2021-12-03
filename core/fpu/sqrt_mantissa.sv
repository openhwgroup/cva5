import taiga_config::*;
import riscv_types::*;
import taiga_types::*;
import fpu_types::*;

module sqrt_mantissa #(ITERATION = 50) (
  input logic clk,
  input logic rst,
  unsigned_sqrt_interface.sqrt sqrt
  );

  logic running;
  logic terminate;
  int counter;

  localparam Q_W = sqrt.DATA_WIDTH >> 1; 
  localparam CLZ_W = $clog2(sqrt.DATA_WIDTH);
  int iteration, active_data_width;

  ////////////////////////////////////////////////////
  //Control Signals
  assign active_data_width = sqrt.DATA_WIDTH - (32'(radicand_clz) - 32'(odd));
  assign iteration = active_data_width >> 1;

  always_ff @ (posedge clk) begin
    if (rst)
      running <= 0;
    else if (sqrt.start)
      running <= 1;
    else if (terminate)
      running <= 0;
  end

  always_ff @ (posedge clk) begin
    sqrt.done <= (running & terminate);
    if (rst)
      counter <= 0;
    else if (sqrt.start)
      counter <= 1; 
    else if (running & ~terminate)
      counter <= counter + 1;
  end

  //assign sqrt.done = terminate & running;
  assign terminate = counter > ITERATION | sqrt.early_terminate;;
  ////////////////////////////////////////////////////
  //Implementation

  ////////////////////////////////////////////////////
  //Normalize radicand
  logic [CLZ_W-1:0] radicand_clz;
  logic odd;
  int i;
  logic [sqrt.DATA_WIDTH-1:0] normalized_radicand;
  //clz clz_radicand (.clz_input(sqrt.radicand), .clz(radicand_clz));
  always_comb begin
    for (i = 0; i < FRAC_WIDTH; i++) begin 
      if (sqrt.radicand[sqrt.DATA_WIDTH-1-i] == 1) begin 
        break;
      end 
    end
    radicand_clz = i[CLZ_W-1:0];
  end

  assign odd = radicand_clz[0];
  assign normalized_radicand = sqrt.radicand << (radicand_clz - CLZ_W'(odd));

  ////////////////////////////////////////////////////
  //Subtraction
  logic [sqrt.DATA_WIDTH-1:0] rad, next_rad;
  logic [sqrt.DATA_WIDTH-1:0] current_dividend, next_dividend;
  logic [sqrt.DATA_WIDTH-1:0] divisor, subtraction;

  assign divisor = (sqrt.DATA_WIDTH)'({sqrt.quotient[sqrt.DATA_WIDTH-3:0], 2'b01});
  assign subtraction = current_dividend - divisor;

  ////////////////////////////////////////////////////
  //Next Working Dividend Determination
  logic overflow;
  assign overflow = subtraction[sqrt.DATA_WIDTH-1];
  always_comb begin
    if (overflow) 
      next_dividend = {current_dividend[sqrt.DATA_WIDTH-3:0], rad[sqrt.DATA_WIDTH-1-:2]};
    else
      next_dividend = {subtraction[sqrt.DATA_WIDTH-3:0], rad[sqrt.DATA_WIDTH-1-:2]};
  end

  always_ff @ (posedge clk) begin
    if (sqrt.start) 
      //first working dividend if the upper 2 bits of the radicand
      current_dividend <= sqrt.DATA_WIDTH'(normalized_radicand[sqrt.DATA_WIDTH-1-:2]);
    else if(~terminate & running)
      current_dividend <= next_dividend;
  end

  ////////////////////////////////////////////////////
  //Update remaining radicand digits
  //TODO: can optimize to just shift left on posedge clk
  assign next_rad = {rad[sqrt.DATA_WIDTH-3:0], 2'b0};  

  always_ff @ (posedge clk) begin
    if (sqrt.start) 
      //the upper two bits are pushed to the working dividend register
      rad <= {normalized_radicand[sqrt.DATA_WIDTH-3:0], 2'b00};
    else if(~terminate & running) 
      rad <= next_rad;
  end

  ////////////////////////////////////////////////////
  //Quotient Determination
  logic [sqrt.DATA_WIDTH-1:0] Q, new_Q;
  logic new_Q_bit;

  assign new_Q_bit = ~overflow;
  assign new_Q = {sqrt.quotient[0+:sqrt.DATA_WIDTH-1], new_Q_bit};

  always_ff @ (posedge clk) begin
    if (sqrt.start) begin
      sqrt.quotient <= '0;
      sqrt.remainder <= '0;
    end else if (~terminate & running) begin
      sqrt.quotient <= sqrt.DATA_WIDTH'(new_Q); 
      sqrt.remainder <= next_dividend;
    end
  end 

  ////////////////////////////////////////////////////
  //End of Implementation
  ////////////////////////////////////////////////////

endmodule


