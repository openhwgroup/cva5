import debug_cfg_types::*;

module debug_module (
        input logic rst,
        input logic clk,

        dmi_cpu_interface.dmi debug[NUM_CPUS-1:0],
        dmi_interface.dmi jtag,
        
        //SIMULATION ONLY:
        output DM_Status_t DMS_out,
        output DM_control_t DMC_out,
        output abstract_control_and_status_t ACS_out
        );

    genvar index;
    DM_Status_t DMS;
    
    assign DMS.zero1 = 0;
    assign DMS.zero2 = 0;
    assign DMS.zero3 = 0;
    assign DMS.cfgstrvalid = 0;
    assign DMS.impebreak = 0;
    //DMS Constants
    assign DMS.authenticated = 1;//no authentication
    assign DMS.authbusy = 0;
    assign DMS.version = 2; //version 0.13
    assign DMS_out = DMS;
    DM_control_t DMC;
    //assign DMC.zero1 = 0;
    //assign DMC.zero2 = 0;

    //read-only reg
    //same for all Taiga cores

    hart_info_t hart_info;
    assign hart_info.zero1 = 0;
    assign hart_info.zero2 = 0;
    assign hart_info.nscratch = 2;
    assign hart_info.dataaccess = 0;
    assign hart_info.datasize = 3;
    assign hart_info.dataaddr = 0;
    
    assign DMC_out = DMC;
    //read-only reg
    //Only support < 32 cores
    logic [31:0] halt_summary;
    assign halt_summary[31:1] = '0;
    assign halt_summary[0] = DMS.anyhalted;

    //read-write reg
    //Only support < 32 cores
    logic [31:0] hart_array_window_select;
    //assign hart_array_window_select = 0;

    //read-write reg
    logic [31:0] hart_array_window;

    //read-only and read-write reg

    abstract_control_and_status_t ABS_CS;
    assign ABS_CS.zero1 = 0;
    assign ABS_CS.zero2 = 0;
    assign ABS_CS.zero3 = 0;
    assign ABS_CS.zero4 = 0;
    assign ABS_CS.datacount = 2;
    assign ABS_CS.progsize = 16;
    assign ACS_out = ABS_CS;
    //write-only reg
    typedef struct packed{
        logic [31:24] cmdtype;
        logic [23:0] control;
    } abstract_command_t;
    abstract_command_t ABS_COMMAND;

    //abstract command autoexec, unused

    //read-only
    logic[31:0] cfg_addr0;

    //read-write
    logic[31:0] abstract_data [2:0];

    //LUT-RAM
    logic[31:0] program_buffer [7:0];
    logic[31:0] program_buffer_output;

    logic [31:0] data_out;
    
    logic write_request;
    logic new_DMC_req;
    //Implementation
    //////////////////////////////////////////////////////////////////
    
    assign write_request = jtag.new_request & ~jtag.rnw;

   
    //DMC
    always_ff @ (posedge clk) begin
        if (rst) begin
            DMC.dmactive <= 0;
            DMC <= 0;
            new_DMC_req <= 0;
        end
        else begin
        DMC.dmactive <= 1;
            if (write_request) begin
                if (jtag.address == DEBUG_MODULE_CONTROL) begin
                    DMC <= jtag.jtag_data;
                    new_DMC_req <= 1;
                end
            end
            else begin
                new_DMC_req <= 0;
            end
        end;
     end
    //Write to registers
    //////////////////
    //HART_ARRAY_WINDOW_SELECT
    always_ff @ (posedge clk) begin
    if (rst) 
        hart_array_window_select <= 0;
    else
        if(write_request & jtag.address == HART_ARRAY_WINDOW_SELECT) 
            hart_array_window_select <= jtag.jtag_data;          
     end  
    
    //HART_ARRAY_WINDOW
    always_ff @ (posedge clk) begin
    if (rst) 
        hart_array_window <= 0;
    else
        if(write_request & jtag.address == HART_ARRAY_WINDOW) 
            hart_array_window <= jtag.jtag_data;          
    end  
    //Selected Harts (hasel,hartsel)-----------------------------------------
    logic[31:0] hartsel_mask;
    logic[HARTSELLEN:0] selected_hart;
    assign selected_hart = {DMC.hartselhi,DMC.hartsello}; //Index-based
    generate
    
    //for (index = 0; index < NUM_CPUS; index=index+1) begin
    for (index = 0; index < 32; index=index+1) begin
        always_comb begin
            if(selected_hart == index)
                hartsel_mask[index] <= 1; //convert index to mask
            else
                hartsel_mask[index] <= 0;
        end
    end
    endgenerate
    
    logic[31:0] selected_harts;
    always_comb begin
        if(~DMC.hasel)
            selected_harts <= hartsel_mask;
        else     
            selected_harts <= hartsel_mask | hart_array_window;
    end 
    
    //ABS_COMMAND
    always_ff @ (posedge clk) begin
    if (rst) 
        ABS_COMMAND <= 0;
    else
        if(write_request & jtag.address == ABSTRACT_COMMAND) 
            ABS_COMMAND <= jtag.jtag_data;          
    end
    //ABS_DATA0------------return data for abstract commands
    logic[31:0][NUM_CPUS-1:0] abs_cmd_return;
    logic[NUM_CPUS-1:0] abs_cmd_sig;
    generate  
    for (index = 0; index < NUM_CPUS; index=index+1) begin
        always_ff @(posedge clk) begin
            if (rst) begin
                abs_cmd_return[index] <= 0;
                abs_cmd_sig[index] <= 0;
            end
            else begin
                if(debug[index].rnw_ack && debug[index].rnw) begin
                    abs_cmd_return[index] <= debug[index].read_data;
                    abs_cmd_sig[index] <= 1;              
                end
                else begin
                    abs_cmd_return[index] <= 0;
                    abs_cmd_sig[index] <= 0;  
                end
            end
        end
    end
    endgenerate
    
    always_ff @ (posedge clk) begin
    if (rst) 
        abstract_data[0] <= 0;
    else
        if(write_request & jtag.address == ABSTRACT_DATA0) 
            abstract_data[0] <= jtag.jtag_data;
        else if(|abs_cmd_sig) 
            abstract_data[0] <= abs_cmd_return[selected_hart]; //PROBLEM: THIS NEEDS TO BE OBTAINED FROM THE CORRECT PROCESSOR
    end
    //ABS_DATA1
    always_ff @ (posedge clk) begin
    if (rst) 
        abstract_data[1] <= 0;
    else
        if(write_request & jtag.address == ABSTRACT_DATA1) 
            abstract_data[1] <= jtag.jtag_data;          
    end
    
    //ABS_DATA2
    always_ff @ (posedge clk) begin
    if (rst) 
        abstract_data[2] <= 0;
    else
        if(write_request & jtag.address == ABSTRACT_DATA2) 
            abstract_data[2] <= jtag.jtag_data;          
    end
    //////////////////
    
    //program_buffer
    always_ff @ (posedge clk) begin
        if (write_request && jtag.address >= 7'h20 &&  jtag.address < 7'h30)
            program_buffer[jtag.address[3:0]] <= jtag.jtag_data;
    end
    assign program_buffer_output = program_buffer[jtag.address[3:0]];

    //read mux
    always_comb begin
        case(jtag.address)
            ABSTRACT_DATA0 : data_out <= abstract_data[0];
            ABSTRACT_DATA1  : data_out <= abstract_data[1];
            ABSTRACT_DATA2  : data_out <= abstract_data[2];
            DEBUG_MODULE_CONTROL : data_out <= DMC;
            DEBUG_MODULE_STATUS  : data_out <= DMS;
            HART_INFO  : data_out <= hart_info;
            HALT_SUMMARY : data_out <= halt_summary;
            HART_ARRAY_WINDOW_SELECT : data_out <= hart_array_window_select;
            HART_ARRAY_WINDOW : data_out <= hart_array_window;
            ABSTRACT_CONTROL_AND_STATUS : data_out <= ABS_CS;
            ABSTRACT_COMMAND : data_out <= ABS_COMMAND;
            ABSTRACT_COMMAND_AUTOEXEC : data_out <= '0;
            CONFIG_STRING_ADDR0 : data_out <= '0;
            CONFIG_STRING_ADDR1 : data_out <= '0;
            CONFIG_STRING_ADDR2 : data_out <= '0;
            CONFIG_STRING_ADDR3 : data_out <= '0;
            PROGRAM_BUFFER0 : data_out <= program_buffer_output;
            PROGRAM_BUFFER1 : data_out <= program_buffer_output;
            PROGRAM_BUFFER2 : data_out <= program_buffer_output;
            PROGRAM_BUFFER3 : data_out <= program_buffer_output;
            PROGRAM_BUFFER4 : data_out <= program_buffer_output;
            PROGRAM_BUFFER5 : data_out <= program_buffer_output;
            PROGRAM_BUFFER6 : data_out <= program_buffer_output;
            PROGRAM_BUFFER7 : data_out <= program_buffer_output;
            PROGRAM_BUFFER8 : data_out <= program_buffer_output;
            PROGRAM_BUFFER9 : data_out <= program_buffer_output;
            PROGRAM_BUFFER10 : data_out <= program_buffer_output;
            PROGRAM_BUFFER11 : data_out <= program_buffer_output;
            PROGRAM_BUFFER12 : data_out <= program_buffer_output;
            PROGRAM_BUFFER13 : data_out <= program_buffer_output;
            PROGRAM_BUFFER14 : data_out <= program_buffer_output;
            PROGRAM_BUFFER15 : data_out <= program_buffer_output;
            default :  data_out <= '0;
        endcase
    end

    always_ff @ (posedge clk) begin
        jtag.handled <= jtag.new_request;
    end        

    assign jtag.response = DMI_STATUS_SUCCESS;
    
    always_ff @ (posedge clk) begin
        jtag.dmi_data <= data_out;
    end    



//Are Cores Running Check-------------------------------------------------------------------------
logic [NUM_CPUS-1:0] all_running_array; 
generate
for (index = 0; index < NUM_CPUS; index=index+1) begin
    always_comb begin
         all_running_array[index] <= debug[index].running;
    end
end
endgenerate

always_ff @ (posedge clk) begin
if (rst) begin
    DMS.allrunning <= 0;
    DMS.anyrunning <= 0;
end
else
    DMS.allrunning  <= &(all_running_array | ~selected_harts) && |selected_harts;
    DMS.anyrunning <= |(all_running_array & selected_harts);
end

//Hart Resets Requests-------------------------------------------------------------------------
//Requests & Acknowledgements-----------------
generate  
for (index = 0; index < NUM_CPUS; index=index+1) begin
    always_ff @(posedge clk) begin
        if (rst)
            debug[index].reset <= 0;
        else begin
            if(DMC.hartreset && new_DMC_req) begin //Send New Requests
                debug[index].reset <= selected_harts[index];

            end
            else if(debug[index].reset_ack == 1 || DMC.hartreset == 0) begin //Wait for Ack OR Debugger has unset the reset bit
                debug[index].reset <= 0;
            end
        end
    end
end
endgenerate
//Status Register Updates-----------------
always_ff @ (posedge clk) begin
if (rst) begin
    DMS.allhavereset <= 0;
    DMS.anyhavereset <= 0;
end
else
    if(DMC.hartreset) begin
       DMS.allhavereset <= 1;
       DMS.anyhavereset <= 1;
    end
    else if(DMC.ackhavereset)begin //clear only if Debugger has acknowledge the reset
        DMS.allhavereset  <= 0;
        DMS.anyhavereset <= 0;
    end 
end

//Halt RequestsRequests-------------------------------------------------------------------------
//Requests & Acknowledgements-----------------
generate  
for (index = 0; index < NUM_CPUS; index=index+1) begin
    always_ff @(posedge clk) begin
        if (rst)
            debug[index].halt <= 0;
        else begin
            if(DMC.haltreq && new_DMC_req) begin //Send New Requests
                debug[index].halt <= selected_harts[index];
           end
           else if(ABS_COMMAND.cmdtype == 1 && debug[index].running) //From Abstract Command
                debug[index].halt <= hartsel_mask[index];
            else if(debug[index].halt_ack == 1) begin //Wait for Ack
                debug[index].halt <= 0;
            end
        end
    end
end
endgenerate
//Status Register Updates--------------------
always_ff @ (posedge clk) begin
if (rst) begin
    DMS.allhalted <= 0;
    DMS.anyhalted <= 0;
end
else
    DMS.allhalted  <= &(~all_running_array | ~selected_harts) && |selected_harts;
    DMS.anyhalted <= |(~all_running_array & selected_harts);
end

//Resume Requests-------------------------------------------------------------------------
//Requests & Acknowledgements-----------------
generate  
for (index = 0; index < NUM_CPUS; index=index+1) begin
    always_ff @(posedge clk) begin
        if (rst)
            debug[index].resume <= 0;
        else begin
            if(DMC.resumereq && new_DMC_req && ~DMC.haltreq) begin //Send New Requests
                debug[index].resume <= selected_harts[index];

            end
            else if(debug[index].resume_ack == 1) begin //Wait for Ack
                debug[index].resume <= 0;
            end
        end
    end
end
endgenerate
//Status Register Updates--------------------NOTE: This checks for the ACKS not the current status
logic [NUM_CPUS-1:0] all_resume_ack_array; 
generate
for (index = 0; index < NUM_CPUS; index=index+1) begin
    always_comb begin
        if(DMC.resumereq && selected_harts[index]  && ~DMC.haltreq && new_DMC_req) //if a new request is sent, reset the bit
            all_resume_ack_array[index] <= 0;
        if(debug[index].resume_ack) //only set bit if the ack has been recieved
            all_resume_ack_array[index] <= 1;
    end
end
endgenerate

always_ff @ (posedge clk) begin
if (rst) begin
    DMS.allresumeack <= 0;
    DMS.anyresumeack <= 0;
end
else
    if(DMC.resumereq) begin 
        DMS.allresumeack  <= &(all_resume_ack_array|~selected_harts) && |selected_harts;
        DMS.anyresumeack <= |(all_resume_ack_array & selected_harts);  
    end
    else begin // Do I need to set this to 0?
        DMS.allresumeack <= 0;
        DMS.anyresumeack <= 0;
    end
        
end
//ALL/ANY nonexistent,allunavailallunavail------------

logic [31:0] non_exist_array;
generate
for (index = 0; index < 32; index=index+1) begin
    always_comb begin
        if(index > NUM_CPUS)
            non_exist_array[index] <= 1;
        else
            non_exist_array[index] <= 0;
    end
end
endgenerate

always_ff @ (posedge clk) begin
if (rst) begin
    DMS.allnonexistent <= 0;
    DMS.anynonexistent <= 0;
    DMS.allunavail <= 0;
    DMS.anyunavail <= 0;
end
else begin
    DMS.allnonexistent  <= &(non_exist_array|~selected_harts) && |selected_harts;
    DMS.anynonexistent <= |(non_exist_array & selected_harts); 
    //DMS.allunavail  <= &(non_exist_array|~selected_harts) && |selected_harts;
    //DMS.anyunavail <= |(non_exist_array & selected_harts);   
end       
end

//Abtract Commands----------------------------------------------------------------
//TO-DO: DID WE IMPLEMENT POSTEXEC
logic new_ABSTRACT_req;
always_ff @ (posedge clk) begin
if (rst) begin
    new_ABSTRACT_req <= 0;
end
else begin
    if (write_request && jtag.address == ABSTRACT_COMMAND) begin
        new_ABSTRACT_req <= 1;
    end
    else begin
        new_ABSTRACT_req <= 0;
    end
end
end

logic [NUM_CPUS-1:0] abstract_ack_array; 
generate
for (index = 0; index < NUM_CPUS; index=index+1) begin
    always_comb begin
        if(new_ABSTRACT_req && hartsel_mask[index]) //if a new request is sent, reset the bit
            abstract_ack_array[index] <= 0;
        if(debug[index].rnw_ack) //only set bit if the ack has been recieved
            abstract_ack_array[index] <= 1;
    end
end
endgenerate

//Requests-----------------
logic[31:0][NUM_CPUS-1:0] program_buffer_addr;
logic execute_program_buffer;
logic [NUM_CPUS-1:0]execute_program_buffer_postexec;
logic [NUM_CPUS-1:0]execute_program_buffer_auto;
logic [NUM_CPUS-1:0]new_execute_program_buffer_req;
assign execute_program_buffer = |execute_program_buffer_postexec | |execute_program_buffer_auto; //note do we need a hartsel_mask here?

generate  
for (index = 0; index < NUM_CPUS; index=index+1) begin
    always_comb begin
        program_buffer_addr[index] <= debug[index].program_buffer_addr;
    end
end
endgenerate
logic halted_hartsel;
assign halted_hartsel = |(hartsel_mask && ~all_running_array);
always_ff @ (posedge clk) begin
    if (rst) begin
        ABS_CS.busy <= 0;
        ABS_CS.cmderr <= 0;
    end
    else begin
        if(ABS_COMMAND.cmdtype == 0 && ABS_COMMAND[22:20] != 2 && new_ABSTRACT_req) begin //If the size of the command is > 32
            ABS_CS.busy <= 0;
            ABS_CS.cmderr <= 2;
        end
        else if(ABS_COMMAND.cmdtype == 0 &&  (ABS_COMMAND[15:0] !=  DEBUG_CSR && ABS_COMMAND[15:0] != DEBUG_PC && ABS_COMMAND[15:0] != DEBUG_SCRATCH1 && ABS_COMMAND[15:0] != DEBUG_SCRATCH2) && new_ABSTRACT_req) begin //Address not readable
            ABS_CS.busy <= 0;
            ABS_CS.cmderr <= 2; 
        end
        else if(ABS_COMMAND.cmdtype == 1 && halted_hartsel) begin //If quick access is the abstract command, but the core is already halted
            ABS_CS.busy <= 0;
            ABS_CS.cmderr <= 2; 
        end
        else if(ABS_COMMAND.cmdtype == 0 && ABS_COMMAND[17] && ~ABS_COMMAND[16] && new_ABSTRACT_req) begin //Transfer
            ABS_CS.busy <= 1;
            ABS_CS.cmderr <= 0;
        end
        else if(ABS_COMMAND.cmdtype == 0 && ABS_COMMAND[17] && ABS_COMMAND[16] && new_ABSTRACT_req) begin //Write
            ABS_CS.busy <= 1;
            ABS_CS.cmderr <= 0;
        end
        else if(ABS_COMMAND.cmdtype == 1 && ABS_COMMAND[17] && ABS_COMMAND[16] && new_ABSTRACT_req) begin //Write
            ABS_CS.busy <= 1;
            ABS_CS.cmderr <= 0;
        end
        else if(|abstract_ack_array && ~ABS_COMMAND[18]) begin //CASE 1: no execution of program buffer
            ABS_CS.busy <= 0;
            ABS_CS.cmderr <= 0;
        end
        else if(|abstract_ack_array && ABS_COMMAND[18] && program_buffer_addr[selected_hart] == 31'h2F) begin //CASE 2: execution of program buffer. WE have finished the Program Buffer
            ABS_CS.busy <= 0;
            ABS_CS.cmderr <= 0;
        end
    end
end


generate
for (index = 0; index < NUM_CPUS; index=index+1) begin

    always_ff @ (posedge clk) begin
        if (rst) begin
            debug[index].rnw <= 0;
            debug[index].rnw_new_request <= 0;
            execute_program_buffer_postexec[index] <= 0;
            execute_program_buffer_auto [index] <= 0;
            debug[index].write_data <= 0;
            debug[index].read_write_addr <= 0;
        end
        else begin
            execute_program_buffer_postexec[index] <= 0; //Only 1 when rnw_ack has been recieved for the first time and postexec is true
            if(execute_program_buffer) begin //happens in the next cycle after directly above code
                debug[index].write_data <= 31'h20; //write data always comes from data0 register for 32-bits
                debug[index].read_write_addr <= 16'h7b1;
                debug[index].rnw <= 0;
                debug[index].rnw_new_request <= hartsel_mask[index];
                new_execute_program_buffer_req[index] <= 0;
            end    
            else if(ABS_COMMAND.cmdtype == 0 && ABS_COMMAND[17] && ~ABS_COMMAND[16] && new_ABSTRACT_req) begin //Read/Transfer
                debug[index].rnw <= 1;
                debug[index].rnw_new_request <= hartsel_mask[index]; //WE HAVE TO USE ONLY THE HARTSEL MASK AND NOT THE ARRAY MASK
                debug[index].write_data <= abstract_data[0]; //write data always comes from data0 register for 32-bits
                debug[index].read_write_addr <= ABS_COMMAND[15:0];
                if(ABS_COMMAND[18])
                   new_execute_program_buffer_req[index] <= 1;               
            end
            else if(ABS_COMMAND.cmdtype == 0 && ABS_COMMAND[17] && ABS_COMMAND[16] && new_ABSTRACT_req) begin //Write
                debug[index].rnw <= 0;
                debug[index].rnw_new_request <= hartsel_mask[index]; //WE HAVE TO USE ONLY THE HARTSEL MASK AND NOT THE ARRAY MASK
                debug[index].write_data <= abstract_data[0]; //write data always comes from data0 register for 32-bits
                debug[index].read_write_addr <= ABS_COMMAND[15:0];
                if(ABS_COMMAND[18])
                   new_execute_program_buffer_req[index] <= 1;  
            end
            else if(debug[index].rnw_ack) begin
                debug[index].rnw_new_request <= 0;
                if(ABS_COMMAND[18]) begin //postexec
                    if(execute_program_buffer_postexec[index] == 0 && execute_program_buffer_auto [index]== 0 && new_execute_program_buffer_req[index]) begin
                        execute_program_buffer_postexec[index] <= 1; // activation signal
                        new_execute_program_buffer_req[index] <= 0;
                        //execute_program_buffer <= 1; //CANT DO THIS SINCE IT'S A FOR LOOP
                    end
                    else begin
                        //execute_program_buffer <= 1; //CAN'T DO THIS SINCE IT'S A FOR LOOP
                        execute_program_buffer_postexec[index]<= 0; //program bufer execution started
                    end
                end
                else if(ABS_COMMAND.cmdtype == 1) begin //Quick access
                    execute_program_buffer_auto[index]<= 0; //program bufer execution started //ERROR ITS IN A FOR LOOP
                    //execute_program_buffer <= 1;
                end
            end
            else if(ABS_COMMAND.cmdtype == 1 && ~debug[index].running && new_ABSTRACT_req) begin
                execute_program_buffer_auto[index] <= 1;
            end
        end     
    end
end
endgenerate

//Program Buffer - Processor Interface
generate
for (index = 0; index < NUM_CPUS; index=index+1) begin
    always_ff @ (posedge clk) begin
        if (rst) begin
            debug[index].program_buffer_data <= 0;
        end
        else begin
            case(debug[index].program_buffer_addr)
                31'h20 : debug[index].program_buffer_data <= PROGRAM_BUFFER0;
                31'h21 : debug[index].program_buffer_data <= PROGRAM_BUFFER1; 
                31'h22 : debug[index].program_buffer_data <= PROGRAM_BUFFER2; 
                31'h23 : debug[index].program_buffer_data <= PROGRAM_BUFFER3; 
                31'h24 : debug[index].program_buffer_data <= PROGRAM_BUFFER4; 
                31'h25 : debug[index].program_buffer_data <= PROGRAM_BUFFER5; 
                31'h26 : debug[index].program_buffer_data <= PROGRAM_BUFFER6; 
                31'h27 : debug[index].program_buffer_data <= PROGRAM_BUFFER7; 
                31'h28 : debug[index].program_buffer_data <= PROGRAM_BUFFER8; 
                31'h29 : debug[index].program_buffer_data <= PROGRAM_BUFFER9; 
                31'h2A : debug[index].program_buffer_data <= PROGRAM_BUFFER10; 
                31'h2B : debug[index].program_buffer_data <= PROGRAM_BUFFER11; 
                31'h2C : debug[index].program_buffer_data <= PROGRAM_BUFFER12; 
                31'h2D : debug[index].program_buffer_data <= PROGRAM_BUFFER13; 
                31'h2E : debug[index].program_buffer_data <= PROGRAM_BUFFER14; 
                31'h2F : debug[index].program_buffer_data <= PROGRAM_BUFFER15; 
                default : debug[index].program_buffer_data <= 0;
            endcase
            
        end
    end
end
endgenerate
endmodule