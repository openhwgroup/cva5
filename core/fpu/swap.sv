import taiga_config::*;
import taiga_types::*;
import l2_config_and_types::*;
import fpu_types::*;

module swap(
    input logic [FLEN-1:0] rs1,
    input logic [FLEN-1:0] rs2,
    input logic rs1_hidden_bit,
    input logic rs2_hidden_bit,
    output logic [FLEN-1:0] swapped_rs1,
    output logic [FLEN-1:0] swapped_rs2,
    output logic swapped_rs1_hidden_bit,
    output logic swapped_rs2_hidden_bit

);
    logic [EXPO_WIDTH-1:0] rs1_expo;
    logic [EXPO_WIDTH-1:0] rs2_expo;
    logic swap;

    ////////////////////////////////////////////////////
    //Implementation
    //Unpack
    assign rs1_expo = rs1[FLEN-2-:EXPO_WIDTH];
    assign rs2_expo = rs2[FLEN-2-:EXPO_WIDTH];

    generate if (ENABLE_SUBNORMAL) begin
        assign swap = rs1_expo < rs2_expo;
        always_comb begin
            if (swap) begin
                swapped_rs1 = rs2;
                swapped_rs2 = rs1;
                swapped_rs1_hidden_bit = rs2_hidden_bit;
                swapped_rs2_hidden_bit = rs1_hidden_bit;
            end else begin
                swapped_rs1 = rs1;
                swapped_rs2 = rs2;
                swapped_rs1_hidden_bit = rs1_hidden_bit;
                swapped_rs2_hidden_bit = rs2_hidden_bit;
            end
        end
    end else begin
        assign swapped_rs1 = rs1;
        assign swapped_rs2 = rs2;
        assign swapped_rs1_hidden_bit = rs1_hidden_bit;
        assign swapped_rs2_hidden_bit = rs2_hidden_bit;
    end endgenerate
endmodule


