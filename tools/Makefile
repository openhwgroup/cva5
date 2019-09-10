

#MAKEFLAGS += --silent
-include internal.mak
MAKEFILE_DIR=$(pwd)
TAIGA_DIR=/home/ematthew/taiga

RISCV_PREFIX   ?= riscv32-unknown-elf-


#Verilator parameters
###############################################################
VERILATOR_DIR=$(TAIGA_DIR)/test_benches/verilator

TAIGA_SRCS = $(shell cat taiga_compile_order)

VERILATOR_LINT_IGNORE= -Wno-LITENDIAN -Wno-SYMRSVDWORD
VERILATOR_CFLAGS =  -CFLAGS "-g0 -Os -march=native -pipe"

VERILATOR_TRACE_FILE="/data/sim-logs/sim_results.vcd"

AR="gcc-ar"
RANLIB="gcc-ranlib"
export AR
export RANLIB
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

#Binary to Verilog HW init file
###############################################################
ELF_TO_HW_INIT ?= python3 $(TAIGA_DIR)/tools/taiga_binary_converter.py $(RISCV_PREFIX) 0x80000000 131072
###############################################################


define verilator_local_mem_test
	mkdir -p $1
	cp $(VERILATOR_DIR)/TaigaTracer.h $1/
	cp $(VERILATOR_DIR)/TaigaTracer.cc $1/
	cp $(VERILATOR_DIR)/taiga_local_mem.cc $1/
	verilator --cc --exe --Mdir $1 $(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) $(TAIGA_SRCS) \
		 ../test_benches/verilator/taiga_local_mem.sv --top-module taiga_local_mem taiga_local_mem.cc \
		-GMEMORY_FILE=$2
	$(MAKE) -C  $1 -f Vtaiga_local_mem.mk AR="gcc-ar" RANLIB="gcc-ranlib"
	echo $1 > $@
	./$1/Vtaiga_local_mem $3 $4 $(VERILATOR_TRACE_FILE) >> $@
endef

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

#Benchmarks already built
.PHONY : $(EMBENCH_BENCHMARKS)

#Create hw_init files for benchmarks
$(embench_hw) : %.hw_init : %
	$(ELF_TO_HW_INIT) $(EMBENCH_DIR)/build/src/$</$< $@ $<.sim_init

#Run verilator
$(embench_logs) : %_full.log : % $(embench_hw)
	$(call verilator_local_mem_test,$<,\"$(TAIGA_DIR)/tools/$<.hw_init\","/dev/null","/dev/null")

run_embench_verilator: $(embench_logs)
	cat $^ > embench.log

CRUFT= $(EMBENCH_BENCHMARKS) $(embench_hw) $(embench_sim) $(embench_logs) embench.log

#Called by compliance makefile
.PHONY: verilator_taiga_compliance_unit_test
verilator_taiga_compliance_unit_test:
	$(call verilator_local_mem_test,$(COMPLIANCE_BENCHAMRK),\"$(HW_INIT)\", $(LOG_FILE_NAME), $(SIG_FILE_NAME))

.PHONY: verilator_taiga_compliance_tests
run_compliance_tests_verilator:
	$(MAKE) -C $(COMPLIANCE_DIR) clean
	$(MAKE) -C $(COMPLIANCE_DIR) RISCV_TARGET=taiga RISCV_DEVICE=$(COMPLIANCE_TARGET) RISCV_PREFIX=$(RISCV_PREFIX) TAIGA_ROOT=$(TAIGA_DIR)/tools

clean:
	rm -rf $(CRUFT)
