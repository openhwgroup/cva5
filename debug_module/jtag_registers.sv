import debug_cfg_types::*;

module jtag_registers (
        input logic clk,
        output logic reset,
    
        input dtmcs_t current_dtmcs,
        output dtmcs_t updated_dtmcs,
        output update_dtmcs,
    
        input dmi_t current_dmi,
        output dmi_t updated_dmi,
        output update_dmi
        );
    
    jtag_register 
        #( .C_WIDTH($bits(dtmcs_t)), .C_ID(DTMCS_USER_REG))      
        dtmcs_jtag_block
        (
            .clk (clk),
            .reset_out(reset),
            .data_in(current_dtmcs),
            .data_out(updated_dtmcs),
            .new_data(update_dtmcs)
        );
    
    jtag_register 
        #( .C_WIDTH($bits(dmi_t)), .C_ID(DMI_USER_REG))      
        dmi_jtag_block
        (
            .clk (clk),
            .reset_out(),
            .data_in(current_dmi),
            .data_out(updated_dmi),
            .new_data(update_dmi)
        );

endmodule


