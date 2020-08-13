#
# Copyright © 2020  Stuart Hoad, Lesley Shannon
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http:#www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Initial code developed under the supervision of Dr. Lesley Shannon,
# Reconfigurable Computing Lab, Simon Fraser University.
#
# Author(s):
#             Stuart Hoad <shoad@sfu.ca>

# Jasper FPV script for Taiga

clear -all
set_engine_mode {Hp Ht L B I N Tri}

set SCRIPTS_PATH ../../Taiga-dev/formal/scripts
set JG_TAIGA_RTL_PATH ../../Taiga-dev

analyze -sv -f ${SCRIPTS_PATH}/taiga_rtl.vfile 
analyze -sv ${JG_TAIGA_RTL_PATH}/formal/models/taiga_fbm.sv
analyze -sv ${JG_TAIGA_RTL_PATH}/formal/interfaces/axi4_basic_props.sv
analyze -sv ${JG_TAIGA_RTL_PATH}/formal/models/taiga_formal_wrapper.sv
elaborate -top taiga_formal_wrapper \
-bbox_a 17000 -bbox_mul 67 \
-bbox_m sixinput_pop_count

reset rst
clock clk

assume -from_assert <embedded>::taiga_formal_wrapper.u_taiga_fbm.u_ppb_axi.env_*
#assume -env {u_ppb_axi.axi_if.arvalid == 1'b0}
#assume -env {u_ppb_axi.axi_if.awvalid == 1'b0}
