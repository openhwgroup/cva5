package debug_cfg_types;

    parameter DTMCS_USER_REG = 3;
    parameter DMI_USER_REG = 4;
    parameter HARTSELLEN = 9; //hartselo + hartselhi 
    parameter NUM_CPUS = 4;
    //parameter integer ASYNC_CPU [NUM_CPUS-1 : 0]   = {1,1,1,0};
        typedef struct packed{
        logic [31:29] zero1;
        logic [28:24] progsize;
        logic [23:13] zero2;
        logic busy;
        logic zero3;
        logic[10:8] cmderr;
        logic [7:4] zero4;
        logic [3:0] datacount;
    } abstract_control_and_status_t;
    
    typedef struct packed{
        logic [13:0] zero1;
        logic dmihardreset;
        logic dmireset;
        logic zero2;
        logic [2:0] idle;
        logic [1:0] dmistat;
        logic [5:0] abits;
        logic [3:0] version;
    } dtmcs_t;

    typedef struct packed{
        logic [6:0] address;
        logic [31:0] data;
        logic [1:0] op;
    } dmi_t;    
    
      typedef struct packed{
          logic [7:0] cmdtype;
          logic zero1;
          logic [2:0] size;
          logic zero2;
          logic postexec;
          logic transfer;
          logic write;
          logic [15:0] regno;
      } abstract_command_t;    
    
    //Address map
    typedef enum bit [6:0] {
        ABSTRACT_DATA0 = 7'h04,
        ABSTRACT_DATA1 = 7'h05,
        ABSTRACT_DATA2 = 7'h06,
        DEBUG_MODULE_CONTROL = 7'h10,
        DEBUG_MODULE_STATUS = 7'h11,
        HART_INFO = 7'h12,
        HALT_SUMMARY = 7'h13,
        HART_ARRAY_WINDOW_SELECT = 7'h14,
        HART_ARRAY_WINDOW = 7'h15,
        ABSTRACT_CONTROL_AND_STATUS = 7'h16,
        ABSTRACT_COMMAND = 7'h17,
        ABSTRACT_COMMAND_AUTOEXEC = 7'h18,
        CONFIG_STRING_ADDR0 = 7'h19,
        CONFIG_STRING_ADDR1 = 7'h1a,
        CONFIG_STRING_ADDR2 = 7'h1b,
        CONFIG_STRING_ADDR3 = 7'h1c,
        PROGRAM_BUFFER0 = 7'h20,
        PROGRAM_BUFFER1 = 7'h21,
        PROGRAM_BUFFER2 = 7'h22,
        PROGRAM_BUFFER3 = 7'h23,
        PROGRAM_BUFFER4 = 7'h24,
        PROGRAM_BUFFER5 = 7'h25,
        PROGRAM_BUFFER6 = 7'h26,
        PROGRAM_BUFFER7 = 7'h27,
        PROGRAM_BUFFER8 = 7'h28,
        PROGRAM_BUFFER9 = 7'h29,
        PROGRAM_BUFFER10 = 7'h2a,
        PROGRAM_BUFFER11 = 7'h2b,
        PROGRAM_BUFFER12 = 7'h2c,
        PROGRAM_BUFFER13 = 7'h2d,
        PROGRAM_BUFFER14 = 7'h2e,
        PROGRAM_BUFFER15 = 7'h2f
        //auth, serial, system bus unused
    } dm_addr_map_t;
    
    typedef enum bit [15:0] {
        DEBUG_CSR = 16'h7b0,
        DEBUG_PC = 16'h7b1,
        DEBUG_SCRATCH1 = 16'h7b2,
        DEBUG_SCRATCH2 = 16'h7b3
        } riscv_debug_addr_map_t;
        
    typedef enum bit [1:0] {
        DMI_OP_NOP = 2'b00,
        DMI_OP_READ = 2'b01,
        DMI_OP_WRITE = 2'b10,
        DMI_OP_RESERVED = 2'b11
    } dmi_jtag_op_t;    
    
    typedef enum bit [1:0] {
        DMI_STATUS_SUCCESS = 2'b00,
        DMI_STATUS_RESERVED = 2'b01,
        DMI_STATUS_FAILED = 2'b10,
        DMI_STATUS_BUSY = 2'b11
    } dmi_response_op_t;        
        
        //Read only status register
    typedef struct packed{
        logic[31:23] zero1;
        logic impebreak;
        logic[21:20] zero2;
        logic allhavereset;
        logic anyhavereset;
        logic allresumeack;
        logic anyresumeack;
        logic allnonexistent;
        logic anynonexistent;
        logic allunavail;
        logic anyunavail;
        logic allrunning;
        logic anyrunning;
        logic allhalted;
        logic anyhalted;
        logic authenticated;
        logic authbusy;
        logic zero3;//5
        logic cfgstrvalid;
        logic [3:0] version;
    } DM_Status_t;
    
        //read-write register
    typedef struct packed{
        logic haltreq;
        logic resumereq;
        logic hartreset;
        logic ackhavereset;
        logic zero1;
        logic hasel; 
        logic [25:16] hartsello;
        logic [15:6] hartselhi; 
        logic [5:2] zero2;
        logic ndmreset;
        logic dmactive;
    } DM_control_t;
    
        typedef struct packed{
        logic [31:24] zero1;
        logic [23:20] nscratch;
        logic [19:17] zero2;
        logic dataaccess;
        logic [15:12] datasize;
        logic [11:0] dataaddr;
    } hart_info_t;
    
    typedef struct packed {    
        logic [6:0] address;
        logic [31:0] jtag_data;
        logic [31:0] dmi_data;
        logic new_request;
        logic rnw;
        logic handled;
        logic [1:0] response;
    }dmi_interface_t;
    
    typedef struct packed{
        logic [6:0] address;
        logic [31:0] jtag_data;
        logic new_request;
        logic rnw;
    } jtag_commands_t;
endpackage


