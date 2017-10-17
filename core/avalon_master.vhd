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
 
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.numeric_std.ALL;
USE ieee.math_real.log2;
USE ieee.math_real.ceil;
use IEEE.STD_LOGIC_UNSIGNED.ALL;


entity avalon_master is
    Port (
        clk : in std_logic;
        rst : in std_logic;
        
        --Bus ports
        addr : out std_logic_vector(31 downto 0);
        avread : out std_logic;
        avwrite : out std_logic;
        byteenable : out std_logic_vector(3 downto 0);
        readdata : in std_logic_vector(31 downto 0);
        writedata : out std_logic_vector(31 downto 0);
        waitrequest : in std_logic;
        readdatavalid : in std_logic;
        writeresponsevalid : in std_logic;
        
        --L/S interface
        addr_in : in std_logic_vector(31 downto 0);
        data_in : in std_logic_vector(31 downto 0);
        data_out : out std_logic_vector(31 downto 0);
        data_valid : out std_logic;
        ready : out std_logic;
        new_request : in std_logic;
        rnw : in std_logic;
        be : in std_logic_vector(3 downto 0);
        data_ack : in std_logic
    );
end avalon_master;
    
architecture Behavioral of avalon_master is
    signal rnw_r : std_logic;

begin

    process (clk) is
    begin
        if (clk'event and clk = '1') then
            if (new_request = '1') then
                rnw_r <= rnw;
                addr <= addr_in;
            end if;
        end if;
    end process;
    
    process (clk) is
    begin
        if (clk'event and clk = '1') then
            if (rst = '1') then
                ready <= '1';
            elsif (new_request = '1') then
                ready <= '0';
            elsif ((data_ack = '1' and rnw_r = '1') or (waitrequest = '0' and rnw_r = '0')) then
                ready <= '1';
            end if;
        end if;
    end process;


    process (clk) is
    begin
        if (clk'event and clk = '1') then
            if (rst = '1') then
                avread <= '0';
            elsif (new_request = '1' and rnw = '1') then
                avread <= '1';
            elsif (waitrequest = '0') then
                avread <= '0';
            end if;
        end if;
    end process;
    
    process (clk) is
    begin
        if (clk'event and clk = '1') then
            if (rst = '1') then
                avwrite <= '0';
            elsif (new_request = '1' and rnw = '0') then
                avwrite <= '1';
            elsif (waitrequest = '0') then
                avwrite <= '0';
            end if;
        end if;
    end process;
    
    process (clk) is
    begin
        if (clk'event and clk = '1') then
            if (new_request = '1' and rnw = '0') then
                writedata <= data_in;
                byteenable <= be;
            end if;
        end if;
    end process;

    process (clk) is
    begin
        if (clk'event and clk = '1') then
            if (rnw_r = '1' and waitrequest = '0') then
                data_out <= readdata;
            end if;
        end if;
    end process;
    
    process (clk) is
    begin
        if (clk'event and clk = '1') then
            if(rst = '1') then
                data_valid <= '0';
            elsif(data_ack = '1') then
                data_valid <= '0';
            elsif (rnw_r = '1' and waitrequest = '0') then
                data_valid <= '1';
            end if;
        end if;
    end process;
    
    
end Behavioral;

    
    
    
