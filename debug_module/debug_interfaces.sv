interface dmi_interface;
    logic [6:0] address;
    logic [31:0] jtag_data;
    logic [31:0] dmi_data;
    logic new_request;
    logic rnw;
    logic handled;
    logic [1:0] response;

    modport jtag (
            input handled, response, dmi_data,
            output address, jtag_data, new_request, rnw);
    modport dmi (
            output handled, response, dmi_data,
            input address, jtag_data, new_request, rnw);
endinterface


interface dmi_cpu_interface;
    logic halt;
    logic resume;
    logic reset;
    logic halt_ack;
    logic resume_ack;
    logic reset_ack;
    logic halt_ack_recv;
    logic resume_ack_recv;
    logic running;
    logic [31:0] read_data;
    logic [31:0] write_data;
    logic [31:0] read_write_addr;
    logic [3:0] program_buffer_addr;
    logic [31:0] program_buffer_data;
    logic rnw;
    logic rnw_ack;
    logic rnw_new_request;


    modport dmi (
            input halt_ack, resume_ack,program_buffer_addr, reset_ack,running,halt_ack_recv,resume_ack_recv,read_data,rnw_ack,
            output halt, resume,program_buffer_data,reset,write_data,rnw_new_request,rnw,read_write_addr);
    modport cpu (
            output halt_ack, resume_ack,program_buffer_addr, reset_ack,running,halt_ack_recv,resume_ack_recv,read_data,rnw_ack,
            input halt, resume, program_buffer_data,reset,write_data,rnw_new_request,rnw,read_write_addr);
endinterface  