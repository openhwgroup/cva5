
module jtag_register 
        #(
        parameter C_WIDTH = 32,
        parameter C_ID = 3
        )      
        (
        input logic clk,
        output logic reset_out,
        input logic [C_WIDTH-1:0] data_in,
        output logic [C_WIDTH-1:0] data_out,
        output logic new_data
        );

    logic capture, drck_i, tck, drck, reset, sel, shift, tdi, update, tdo;
    logic [C_WIDTH-1:0] captured_data;   
    logic [C_WIDTH-1:0] jtag_data;   
    logic ack;

    localparam SYNC_STAGES = 3;
    logic new_data_sync [SYNC_STAGES-1:0];
    ///////////////////////////////////////////////////////////////////
    
    BUFG drck_bufg (.O(drck), .I(drck_i));    
    
    BSCANE2 #( .JTAG_CHAIN(C_ID))
        bscan  (
            .CAPTURE    (capture),
            .DRCK       (drck_i),
            .RESET      (reset),
            .RUNTEST    (),
            .SEL        (sel),
            .SHIFT      (shift), 
            .TCK        (tck),
            .TDI        (tdi),
            .TMS        (),
            .UPDATE     (update),
            .TDO        (tdo) 
        );
    
    assign reset_out = reset;
    
    //X stage Synchronizers for handshaking
    always_ff @(posedge update or posedge reset or posedge ack) begin
        if (reset | ack)
            new_data_sync[0] <= 0;
        else begin
            if (sel)
                new_data_sync[0] <= 1;
        end    
    end
   
    genvar i;
    generate
        for (i=1; i < SYNC_STAGES; i++) begin    
            always_ff @(posedge clk or posedge reset) begin
                if (reset)
                    new_data_sync[i] <= 0;
                else begin
                    new_data_sync[i] <= new_data_sync[i-1];
                end    
            end              
        end
    endgenerate    
        
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            ack <= 0;
        else begin
            ack <= new_data_sync[SYNC_STAGES-1];
        end    
    end      
    
    assign new_data = ack & ~new_data_sync[SYNC_STAGES-1];
    
    //JTAG Data Register logic as per XAPP139
    always_ff @(posedge drck or posedge reset) begin
        if (reset)
            captured_data <= '0;
        else begin
            if (capture & sel)
                captured_data <= data_in;
            else if (shift & sel)
                captured_data <= {tdi, captured_data[C_WIDTH-1:1]};
        end
    end
    
    always @(posedge update or posedge reset) begin
        if (reset)
            jtag_data <= 0;
        else begin
            if (sel)
                jtag_data <= captured_data;
        end
    end        
    assign data_out = jtag_data;
    assign tdo = captured_data[0];

    
endmodule

