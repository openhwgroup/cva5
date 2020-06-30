

#MAKEFLAGS += --silent
-include internal.mak
MAKEFILE_DIR=$(pwd)
TAIGA_DIR=/home/ematthew/taiga

RISCV_PREFIX   ?= riscv32-unknown-elf-


#Verilator parameters
###############################################################
VERILATOR_DIR=$(TAIGA_DIR)/test_benches/verilator

TAIGA_SRCS = $(shell cat taiga_compile_order)


#Tracing: Set to True or False
TRACE_ENABLE=False
VERILATOR_TRACE_FILE="/data/sim-logs/sim_results.vcd"

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

CFLAGS = -g0 -O3 -march=native -D$(ddr_size_def) -D$(page_size_def) -D$(max_inflight_read_requests) -D$(max_inflight_write_requests)\
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

ifeq ($(LOAD_DDR_FROM_FILE), True)
	VERILATOR_CFLAGS :=  $(VERILATOR_CFLAGS) -D LOAD_DDR_FROM_FILE"
endif

##################################################################################


#Compliance parameters
###############################################################
COMPLIANCE_DIR=/home/ematthew/Research/RISCV/sfu-rcl/taiga-riscv-compliance/
COMPLIANCE_TARGET=rv32im
###############################################################

#Benchmark parameters
#Assumes binaries are in the BENCHMARK_DIR
###############################################################
EMBENCH_DIR=/home/ematthew/Research/RISCV/sfu-rcl/taiga-embench
EMBENCH_BENCHMARKS =  \
aha-mont64 \
crc32 \
cubic \
edn \
huffbench \
matmult-int \
minver \
nbody \
nettle-aes \
nettle-sha256 \
nsichneu \
picojpeg \
qrduino \
sglib-combined \
slre \
st \
statemate \
ud \
wikisort \

 
embench_logs  = $(addsuffix _full.log,  $(EMBENCH_BENCHMARKS))
embench_hw  = $(addsuffix .hw_init,  $(EMBENCH_BENCHMARKS))
embench_sim  = $(addsuffix .sim_init,  $(EMBENCH_BENCHMARKS))
###############################################################

COREMARK_DIR=/home/ematthew/Research/RISCV/software/coremark

#Binary to Verilog HW init file
###############################################################
ELF_TO_HW_INIT ?= python3 $(TAIGA_DIR)/tools/taiga_binary_converter.py $(RISCV_PREFIX) 0x80000000 131072
###############################################################

.PHONY: lint
lint: 
	verilator -cc $(TAIGA_SRCS) \
	../test_benches/verilator/taiga_local_mem.sv \
	--top-module taiga_local_mem \
	--lint-only

.PHONY: lint_full
lint_full:
	verilator -cc $(TAIGA_SRCS) \
	../test_benches/verilator/taiga_local_mem.sv \
	--top-module taiga_local_mem \
	--lint-only -Wall

.PHONY: build_embench
build_embench :
	cd $(EMBENCH_DIR);\
	rm -rf build;\
	mkdir build;\
	cd build;\
	../configure --host=riscv32-unknown-elf --with-chip=speed-test --with-board=taiga-sim;\
	make


.PHONY: build_coremark
build_coremark:
	$(MAKE) -C  $(COREMARK_DIR) compile PORT_DIR=taiga-sim ITERATIONS=5000
	cd $(MAKEFILE_DIR);
	$(ELF_TO_HW_INIT) $(COREMARK_DIR)/coremark.bin coremark.hw_init coremark.sim_init

.PHONY: run_coremark_verilator
run_coremark_verilator :
	./build_taiga_sim/Vtaiga_local_mem "/dev/null" "/dev/null" $(TAIGA_DIR)/tools/coremark.hw_init $(VERILATOR_TRACE_FILE) > $@


#Benchmarks already built
.PHONY : $(EMBENCH_BENCHMARKS)

#Create hw_init files for benchmarks
$(embench_hw) : %.hw_init : %
	$(ELF_TO_HW_INIT) $(EMBENCH_DIR)/build/src/$</$< $@ $<.sim_init

build_taiga_sim: $(TAIGA_SRCS)
	mkdir -p $@
	cp $(VERILATOR_DIR)/TaigaTracer.h $@/
	cp $(VERILATOR_DIR)/TaigaTracer.cc $@/
	cp $(VERILATOR_DIR)/SimMem.h $@/
	cp $(VERILATOR_DIR)/SimMem.cc $@/
	cp $(VERILATOR_DIR)/taiga_local_mem.cc $@/
	cp $(VERILATOR_DIR)/AXI_DDR_simulation/axi_ddr_sim.cc $@/
	cp $(VERILATOR_DIR)/AXI_DDR_simulation/axi_ddr_sim.h $@/
	cp $(VERILATOR_DIR)/AXI_DDR_simulation/ddr_page.cc $@/
	cp $(VERILATOR_DIR)/AXI_DDR_simulation/ddr_page.h $@/
	cp $(VERILATOR_DIR)/AXI_DDR_simulation/axi_interface.h $@/
	verilator --cc --exe --Mdir $@ -DENABLE_SIMULATION_ASSERTIONS --assert $(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) $(TAIGA_SRCS) \
		 ../test_benches/verilator/taiga_local_mem.sv --top-module taiga_local_mem taiga_local_mem.cc ddr_page.cc SimMem.cc
	$(MAKE) -C  $@ -f Vtaiga_local_mem.mk

#Run verilator
$(embench_logs) : %_full.log : % $(embench_hw) build_taiga_sim
	@echo $< > $@
	./build_taiga_sim/Vtaiga_local_mem "/dev/null" "/dev/null" $(TAIGA_DIR)/tools/$<.hw_init $(VERILATOR_TRACE_FILE) >> $@

run_embench_verilator: $(embench_logs)
	cat $^ > embench.log

CRUFT= $(EMBENCH_BENCHMARKS) $(embench_hw) $(embench_sim) $(embench_logs) embench.log build_taiga_sim

#Called by compliance makefile
.PHONY: verilator_taiga_compliance_unit_test
verilator_taiga_compliance_unit_test: build_taiga_sim
	./build_taiga_sim/Vtaiga_local_mem $(LOG_FILE_NAME) $(SIG_FILE_NAME) $(HW_INIT) $(VERILATOR_TRACE_FILE) >> $@

.PHONY: verilator_taiga_compliance_tests
run_compliance_tests_verilator: build_taiga_sim
	$(MAKE) -C $(COMPLIANCE_DIR) clean
	$(MAKE) -C $(COMPLIANCE_DIR) RISCV_TARGET=taiga RISCV_DEVICE=$(COMPLIANCE_TARGET) RISCV_PREFIX=$(RISCV_PREFIX) TAIGA_ROOT=$(TAIGA_DIR)/tools

.PHONY: run_dhrystone_verilator
run_dhrystone_verilator : build_taiga_sim
	./build_taiga_sim/Vtaiga_local_mem "/dev/null" "/dev/null" /home/ematthew/Research/RISCV/software/taiga-benchmarks/dhrystone.riscv.hw_init $(VERILATOR_TRACE_FILE) > $@

clean:
	rm -rf $(CRUFT)
