/*
 * Copyright © 2018 Eric Matthews,  Lesley Shannon
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
 *             Yuhui Gao <yuhuig@sfu.ca>
 */

module clz_tree(
  input logic [63:0] clz_input,
  output logic [5:0] clz
);
  logic [63:0] encoded_input;
  logic [6:0] clz_plus1;
  genvar i;

  // encode the input
  generate begin
    for (i = 0; i < 32; i++) begin
      encode enc (clz_input[2*i+1:2*i], encoded_input[2*i+1:2*i]);
    end
  end endgenerate
   
  // compress 2 -> 3
  logic [16*3-1:0] compressed_3bit_vector; // 16 3-bit vector
  generate begin
    for (i = 0; i < 16; i++) begin
      merge #(.N(2)) merge_2to3(encoded_input[i*4+3:i*4], compressed_3bit_vector[i*3+2:i*3]);
    end
  end endgenerate
  
  // compress 3 -> 4
  logic [8*4-1:0] compressed_4bit_vector; // 8 4-bit vector
  generate begin
    for (i = 0; i < 8; i++) begin
      merge #(.N(3)) merge_3to4 (compressed_3bit_vector[i*6+5:i*6], compressed_4bit_vector[i*4+3:i*4]);
    end
  end endgenerate

  // compress 4 -> 5
  logic [4*5-1:0] compressed_5bit_vector; // 4 5-bit vector
  generate begin
    for (i = 0; i < 4; i++) begin
      merge #(.N(4)) merge_4to5 (compressed_4bit_vector[i*8+7:i*8], compressed_5bit_vector[i*5+4:i*5]);
    end
  end endgenerate
  
  // compress 5 -> 6
  logic [2*6-1:0] compressed_6bit_vector; // 2 6-bit vector
  generate begin
    for (i = 0; i < 2; i++) begin
      merge #(.N(5)) merge_5to6 (compressed_5bit_vector[i*10+9:i*10], compressed_6bit_vector[i*6+5:i*6]);
    end
  end endgenerate

  // final 2x1 compression
  merge #(.N(6)) merge_6to7 (compressed_6bit_vector, clz_plus1);
  assign clz = clz_plus1[5:0];

endmodule


module encode(
  input logic [1:0] in,
  output logic [1:0] out
);

  always_comb begin
    case(in)
      2'b00: out = 2'b10;
      2'b01: out = 2'b01;
      default: out = 2'b00;
    endcase
  end
endmodule

module merge # (parameter N = 2, parameter WO = N + 1) (
  input logic [2*N-1:0] in,
  output logic [WO-1:0] out
  );

  always_comb begin
    if (in[2*N-1] == 1'b0) begin
      out[WO-1] = in[2*N-1] & in[N-1]; //can be optimized?
      out[WO-2] = 1'b0;
      out[WO-3:0] = in[2*N-2:N];
    end else begin
      out[WO-1] = in[2*N-1] & in[N-1];
      out[WO-2] = ~in[N-1];
      out[WO-3:0] = in[N-2:0];
    end
  end

endmodule
