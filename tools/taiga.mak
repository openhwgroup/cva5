
###############################################################
VERILATOR_DIR=$(TAIGA_DIR)/test_benches/verilator

# Sources for verilator
TAIGA_HW_SRCS = $(addprefix $(TAIGA_DIR)/, $(shell cat $(TAIGA_DIR)/tools/taiga_compile_order))
TAIGA_SIM_SRCS = $(addprefix $(VERILATOR_DIR)/, TaigaTracer.cc SimMem.cc taiga_sim.cc AXI_DDR_simulation/axi_ddr_sim.cc AXI_DDR_simulation/ddr_page.cc)
TAIGA_INCLUDED_SIM_SRCS = $(addprefix $(VERILATOR_DIR)/, taiga_sim.cc AXI_DDR_simulation/ddr_page.cc SimMem.cc)


#Tracing: Set to True or False
TRACE_ENABLE?=False


#Simulation Binary Name
TAIGA_SIM_DIR?=$(VERILATOR_DIR)/build
TAIGA_SIM?=$(TAIGA_SIM_DIR)/taiga-sim

#DDR Pre-Initialization
LOAD_DDR_FROM_FILE = False
DDR_FILE = "\"path_to_DDR_init_file\""
DDR_FILE_STARTING_LOCATION = 0
DDR_FILE_NUM_BYTES = 0

#AXI DDR Parameters
DDR_SIZE_GB = 4
PAGE_SIZE_KB = 2
MAX_READ_REQ = 8
MAX_WRITE_REQ = $(MAX_READ_REQ)
MIN_RD_DELAY = 1
MAX_RD_DELAY = 1
MIN_WR_DELAY = 1
MAX_WR_DELAY = 1
DELAY_SEED = 867583
######################################################################
ddr_size_def = DDR_SIZE=\(long\)$(DDR_SIZE_GB)*\(long\)1073741824
page_size_def = PAGE_SIZE=\($(PAGE_SIZE_KB)*1024\)
max_inflight_read_requests = MAX_INFLIGHT_RD_REQ=$(MAX_READ_REQ)
max_inflight_write_requests = MAX_INFLIGHT_WD_REQ=$(MAX_WRITE_REQ)
mix_delay_read = MIN_DELAY_RD=$(MIN_RD_DELAY)
max_delay_read = MAX_DELAY_RD=$(MAX_RD_DELAY)
min_delay_write = MIN_DELAY_WR=$(MIN_WR_DELAY)
max_delay_write = MAX_DELAY_WR=$(MAX_WR_DELAY)
delay_seed = DELAY_SEED=$(DELAY_SEED)
ddr_init_file = DDR_INIT_FILE=$(DDR_FILE)
ddr_start_loc = DDR_FILE_STARTING_LOCATION=$(DDR_FILE_STARTING_LOCATION)
ddr_num_bytes = DDR_FILE_NUM_BYTES=$(DDR_FILE_NUM_BYTES)

CFLAGS = -g0 -O3 -std=c++11 -march=native -D$(ddr_size_def) -D$(page_size_def) -D$(max_inflight_read_requests) -D$(max_inflight_write_requests)\
	-D$(mix_delay_read) -D$(max_delay_read) -D$(min_delay_write) -D$(max_delay_write) -D$(delay_seed)\
	-D$(ddr_init_file) -D$(ddr_start_loc) -D$(ddr_num_bytes)

#Verilator
################################################################################
VERILATOR_LINT_IGNORE= -Wno-LITENDIAN -Wno-SYMRSVDWORD
ifeq ($(TRACE_ENABLE), True)
	VERILATOR_CFLAGS =  --trace --trace-structs --CFLAGS "$(CFLAGS)  -D TRACE_ON"
else
	VERILATOR_CFLAGS =   --CFLAGS  "$(CFLAGS)"
endif

VERILATOR_LINT_IGNORE= -Wno-LITENDIAN -Wno-SYMRSVDWORD
ifeq ($(LOAD_DDR_FROM_FILE), True)
	VERILATOR_CFLAGS :=  $(VERILATOR_CFLAGS) -D LOAD_DDR_FROM_FILE"
endif

##################################################################################

#taiga_sim included as linter requires top-level to have no interfaces
.PHONY: lint
lint: 
	verilator -cc $(TAIGA_HW_SRCS) \
	$(VERILATOR_DIR)/taiga_sim.sv \
	--top-module taiga_sim \
	--lint-only

.PHONY: lint-full
lint-full:
	verilator -cc $(TAIGA_HW_SRCS) \
	$(VERILATOR_DIR)/taiga_sim.sv \
	--top-module taiga_sim \
	--lint-only -Wall

#Build Taiga Sim
$(TAIGA_SIM): $(TAIGA_HW_SRCS) $(TAIGA_SIM_SRCS)
	mkdir -p $(TAIGA_SIM_DIR)
	verilator --cc --exe --Mdir $(TAIGA_SIM_DIR) -DENABLE_SIMULATION_ASSERTIONS --assert \
		-o taiga-sim \
		$(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) \
		$(TAIGA_INCLUDED_SIM_SRCS) \
		$(TAIGA_HW_SRCS) $(VERILATOR_DIR)/taiga_sim.sv --top-module taiga_sim
	$(MAKE) -C $(TAIGA_SIM_DIR) -f Vtaiga_sim.mk

.PHONY: clean-taiga-sim
clean-taiga-sim:
	rm -rf $(TAIGA_SIM_DIR)

