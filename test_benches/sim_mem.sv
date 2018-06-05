/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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
 *             Eric Matthews <ematthew@sfu.ca>
 */

/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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
 *             Eric Matthews <ematthew@sfu.ca>
 */

package tb_tools;

class sim_mem;
    local logic [31:0] ram [bit [29:0]];
    local string opcodes [bit [29:0]];

    function void load_program (string file_name, integer unsigned base_addr);
        integer program_data;
        integer line_number;
        string string_line;
        string program_asm;
        string program_asm0; //string array for the following usage is not supported by Vivado
        string program_asm1;
        string program_asm2;
        string program_asm3;
        string program_asm4;
        string program_asm5;
        string program_asm6;
        string program_asm7;

        integer scan_result;
        integer read_line_result;
        integer unsigned program_addr;

        integer program_file = $fopen(file_name, "r");
        if (program_file == 0) begin
            $error ("couldn't open file: %s", file_name);
            $finish;
        end

        program_addr = base_addr;
        read_line_result = $fgets (string_line, program_file);
        line_number = 1;

        while (read_line_result !== 0) begin
            program_asm0 = " ";
            program_asm1 = " ";
            program_asm2 = " ";
            program_asm3 = " ";
            program_asm4 = " ";
            program_asm5 = " ";
            program_asm6 = " ";
            program_asm7 = " ";

            scan_result = $sscanf(string_line, "%x %s %s %s %s %s %s %s %s", program_data, program_asm0, program_asm1, program_asm2, program_asm3, program_asm4, program_asm5, program_asm6, program_asm7);

            if (scan_result < 2) begin
                $error ("data file incorrectly formatted on line: %d\n%s", line_number,string_line);
                $finish;
            end

            if (scan_result == 2)
                program_asm = {program_asm0, " "};
            else if (scan_result == 3)
                program_asm = {program_asm0, " ", program_asm1};
            else if (scan_result == 4)
                program_asm = {program_asm0, " ", program_asm1, " ", program_asm2};
            else if (scan_result == 5)
                program_asm = {program_asm0, " ", program_asm1, " ", program_asm2, " ", program_asm3};
            else if (scan_result == 6)
                program_asm = {program_asm0, " ", program_asm1, " ", program_asm2, " ", program_asm3, " ", program_asm4};
            else if (scan_result == 7)
                program_asm = {program_asm0, " ", program_asm1, " ", program_asm2, " ", program_asm3, " ", program_asm4, " ", program_asm5};
            else if (scan_result == 8)
                program_asm = {program_asm0, " ", program_asm1, " ", program_asm2, " ", program_asm3, " ", program_asm4, " ", program_asm5, " ", program_asm6};
            else
                program_asm = {program_asm0, " ", program_asm1, " ", program_asm2, " ", program_asm3, " ", program_asm4, " ", program_asm5, " ", program_asm6, " ", program_asm7};


            this.ram[program_addr[31:2]]= program_data;
            this.opcodes[program_addr[31:2]]= program_asm;

            read_line_result = $fgets (string_line, program_file);
            line_number = line_number + 1;
            program_addr = program_addr + 4;

        end

        $fclose(program_file);
    endfunction

    function logic[31:0] readw (bit[31:0] addr);
        readw = 32'hXXXXXXXX;
        if (this.ram.exists(addr))
            readw = this.ram[addr];
    endfunction

    function string readopcode (bit[31:0] addr);
        readopcode = "not an instruction";
        if (this.opcodes.exists(addr))
            readopcode = this.opcodes[addr];
    endfunction

    function void writew (bit [31:0] addr, logic [31:0] data, logic[3:0] be);
        if(be[0])
            this.ram[addr][7:0] = data[7:0];
        if(be[1])
            this.ram[addr][15:8] = data[15:8];
        if(be[2])
            this.ram[addr][23:16] = data[23:16];
        if(be[3])
            this.ram[addr][31:24] = data[31:24];
    endfunction
endclass

endpackage