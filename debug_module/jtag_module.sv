import debug_cfg_types::*;

module jtag_module (
        input logic clk,
        output logic reset,
        
        dmi_interface.jtag dm
        );

    dtmcs_t dtmcs, dtmcs_jtag;
    dmi_t dmi, dmi_jtag;
    
    logic dtmcs_write;
    logic dmi_write;
    
    logic dmi_busy;   
    logic dmi_error;
    
    jtag_registers jtag_regs(
            .clk(clk),
            .reset(reset),
            .current_dtmcs(dtmcs),
            .updated_dtmcs(dtmcs_jtag),
            .update_dtmcs(dtmcs_write),
                
            .current_dmi(dmi),
            .updated_dmi(dmi_jtag),
            .update_dmi(dmi_write)
        );
    
    //dtmcs register
    assign dtmcs.zero1 = 0;
    assign dtmcs.dmihardreset = 0;
    assign dtmcs.dmireset = 0;    
    assign dtmcs.zero2 = 0;
    assign dtmcs.idle = 20;
    //dmistat
    assign dtmcs.abits = 7;
    assign dtmcs.version = 1;

    always_ff @ (posedge clk) begin
        if (reset)
            dtmcs.dmistat <= DMI_STATUS_SUCCESS;
        else if (dtmcs_write & (dtmcs_jtag.dmireset | dtmcs_jtag.dmihardreset)) //clear error status
            dtmcs.dmistat <= DMI_STATUS_SUCCESS;            
        else if (dmi_write & dmi_busy)
            dtmcs.dmistat <= DMI_STATUS_BUSY;
        else if (dm.handled & ~dmi_error)
            dtmcs.dmistat <= dm.response;
    end
    ////////////////////////////////////////

    always_ff @ (posedge clk) begin
        if (reset)
            dmi_busy <= 0;   
        else if (dtmcs_write & (dtmcs_jtag.dmireset | dtmcs_jtag.dmihardreset))
            dmi_busy <= 0;     
        else if (dmi_write & ~dmi_busy)
            dmi_busy <= 1;
        else if (dm.handled)
            dmi_busy <= 0;        
    end

    always_ff @ (posedge clk) begin
        if (reset)
            dmi_error <= 0;   
        else if (dtmcs_write & (dtmcs_jtag.dmireset | dtmcs_jtag.dmihardreset))
            dmi_error <= 0;     
        else if ((dmi_write & dmi_busy) ||
                (dm.handled && dm.response == DMI_STATUS_FAILED))
                dmi_error <= 1; 
                //dmi_error <= 0; //Test
                 
    end    
    
    //dmi reg
    always_ff @ (posedge clk) begin
        if (reset)
            dmi.address <= 0;   
        else if (dmi_write & ~(dmi_busy | dmi_error))
            dmi.address <= dmi_jtag.address;
    end
    
    always_ff @ (posedge clk) begin
        if (reset)
            dmi.data <= 0;
        else if (dmi_write & ~(dmi_busy | dmi_error) && (dmi_jtag.op == DMI_OP_WRITE))
            dmi.data <= dmi_jtag.data;
        else if (dm.handled)
            dmi.data <= dm.dmi_data;
    end
    
    always_ff @ (posedge clk) begin
        if (reset)
            dmi.op <= DMI_STATUS_SUCCESS;   
        else if (dtmcs_write & (dtmcs_jtag.dmireset | dtmcs_jtag.dmihardreset))
            dmi.op <= DMI_STATUS_SUCCESS;
        else if (dmi_write & ~(dmi_busy | dmi_error))
            dmi.op <= dmi_jtag.op;
        else if (dmi_write & dmi_busy & ~dmi_error)
            dmi.op <= DMI_STATUS_BUSY;
        else if (dm.handled & ~dmi_error)
            dmi.op <= dm.response;
    end
    
    //Output logic
    assign dm.address = dmi.address;
    assign dm.jtag_data = dmi.data;
    
    always_ff @ (posedge clk) begin
        if (dmi_write & ~(dmi_busy | dmi_error))
            dm.rnw <= (dmi_jtag.op == DMI_OP_READ) || (dmi_jtag.op == DMI_OP_NOP);
    end        
        
    always_ff @ (posedge clk) begin
        if (reset)
            dm.new_request <= 0;   
        else if (dmi_write & ~(dmi_busy | dmi_error))
            dm.new_request <= (dmi_jtag.op == DMI_OP_READ) || (dmi_jtag.op == DMI_OP_WRITE) || (dmi_jtag.op == DMI_OP_NOP);
        else
            dm.new_request <= 0;
    end
    
endmodule

