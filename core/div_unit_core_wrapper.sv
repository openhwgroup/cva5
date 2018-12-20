import taiga_config::*;
import taiga_types::*;

module div_unit_core_wrapper 
    #(
        parameter C_WIDTH = 32,
        parameter USE_QUICK_DIV = 0,
        parameter DIV_TYPE = "radix-2"
    )(
        input logic clk,
        input logic rst,
        input logic start,
        input logic ack,
        input logic [C_WIDTH-1:0] A,
        input logic [C_WIDTH-1:0] B,
        output logic [C_WIDTH-1:0] Q,
        output logic [C_WIDTH-1:0] R,
        output logic complete    
    );
    
    logic start_r;
    logic ack_r;
    logic [C_WIDTH-1:0] A_r;
    logic [C_WIDTH-1:0] B_r;
    logic [C_WIDTH-1:0] Q_r;
    logic [C_WIDTH-1:0] R_r;
    logic complete_r;
    logic [C_WIDTH-1:0] Q_o;
    logic [C_WIDTH-1:0] R_o;
    logic complete_o;
    
    always_ff @(posedge clk) begin
        start_r <= start; 
        ack_r   <= ack;
        A_r     <= A;
        B_r     <= B;
        Q_r     <= Q_o;
        R_r     <= R_o;
        complete_r <= complete_o;
    end 
    
    generate
        if (USE_QUICK_DIV) 
            (* keep_hierarchy="yes" *)            
            quickdiv #(XLEN, DIV_TYPE) div_core (
                .clk(clk),
                .rst(rst),
                .start(start_r),
                .ack(ack_r),
                .A(A_r),
                .B(B_r),
                .Q(Q_o),
                .R(R_o),
                .complete(complete_o)
            );
        else
            (* keep_hierarchy="yes" *)
            normdiv #(XLEN, DIV_TYPE) div_core (
                .clk(clk),
                .rst(rst),
                .start(start_r),
                .ack(ack_r),
                .A(A_r),
                .B(B_r),
                .Q(Q_o),
                .R(R_o),
                .complete(complete_o)
            );
    endgenerate

    
    assign Q = Q_r;
    assign R = R_r;
    assign complete = complete_r;
    
endmodule
