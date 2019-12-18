

#MAKEFLAGS += --silent
-include internal.mak
MAKEFILE_DIR=$(pwd)
TAIGA_DIR=/home/ematthew/taiga

RISCV_PREFIX   ?= riscv32-unknown-elf-


#Verilator parameters
###############################################################
VERILATOR_DIR=$(TAIGA_DIR)/test_benches/verilator

TAIGA_SRCS = $(shell cat taiga_compile_order)

#Set to True or False
TRACE_ENABLE=False
VERILATOR_TRACE_FILE="/data/sim-logs/sim_results.vcd"

VERILATOR_LINT_IGNORE= -Wno-LITENDIAN -Wno-SYMRSVDWORD
ifeq ($(TRACE_ENABLE), True)
	VERILATOR_CFLAGS =  --trace -CFLAGS "-g0 -O3 -march=native -D TRACE_ON"
else
	VERILATOR_CFLAGS =  -CFLAGS "-g0 -O3 -march=native"
endif
###############################################################

#Compiance parameters
###############################################################
COMPLIANCE_DIR=/home/ematthew/Research/RISCV/sfu-rcl/taiga-riscv-compliance/
COMPLIANCE_TARGET=rv32im
###############################################################

#Benchmark parameters
#Assumes binaries are in the BENCHMARK_DIR
###############################################################
EMBENCH_DIR=/home/ematthew/Research/RISCV/sfu-rcl/taiga-embench
EMBENCH_BENCHMARKS = \
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
	verilator --cc --exe --Mdir $@ --assert $(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) $(TAIGA_SRCS) \
		 ../test_benches/verilator/taiga_local_mem.sv --top-module taiga_local_mem taiga_local_mem.cc SimMem.cc
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
