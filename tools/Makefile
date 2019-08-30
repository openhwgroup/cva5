

MAKEFLAGS += --silent
MAKEFILE_DIR=$(pwd)
TAIGA_DIR=/home/ematthew/taiga

RISCV_PREFIX   ?= riscv32-unknown-elf-


#Verilator parameters
###############################################################
VERILATOR_DIR=$(TAIGA_DIR)/test_benches/verilator

TAIGA_SRCS = $(shell cat taiga_compile_order)

VERILATOR_LINT_IGNORE= -Wno-UNOPTFLAT -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-LITENDIAN -Wno-SYMRSVDWORD -Wno-CASEINCOMPLETE -Wno-CASEX
VERILATOR_CFLAGS =  -CFLAGS "-g0 -Os -march=native -pipe -flto -Wl,-flto" -LDFLAGS "-flto"

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
BENCHMARK_DIR=/home/ematthew/Research/RISCV/software/taiga-benchmarks/
BENCHMARKS = \
 dhrystone \
 prime \
 rand \
 sqrt \
 micro \
 rsa \
 aes \
 fft \
 qsort \
###############################################################



#Benchmark parameters
#Assumes binaries are in the BENCHMARK_DIR
###############################################################
EMBENCH_DIR=/home/ematthew/Research/RISCV/sfu-rcl/taiga-embench/build/src
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
 
###############################################################

#Binary to Verilog HW init file
###############################################################
ELF_TO_HW_INIT ?= python3 $(TAIGA_DIR)/tools/taiga_binary_converter.py $(RISCV_PREFIX) 0x80000000 131072
###############################################################


COREMARK_DIR=/home/ematthew/Research/RISCV/software/coremark


define verilator_local_mem_test
	mkdir -p $@
	cp $(VERILATOR_DIR)/taiga_local_mem.cc $@/
	verilator -cc --exe --Mdir $@ $(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) $(TAIGA_SRCS) \
		 ../test_benches/verilator/taiga_local_mem.sv --top-module taiga_local_mem taiga_local_mem.cc \
		-GMEMORY_FILE=$1
	$(MAKE) -C  $@ -f Vtaiga_local_mem.mk AR="gcc-ar" RANLIB="gcc-ranlib"
	time ./$@/Vtaiga_local_mem $2 $3
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
		
.PHONY: verilator_taiga_dhrystone
verilator_taiga_dhrystone:
	$(call verilator_local_mem_test,\"$(BENCHMARK_DIR)dhrystone.riscv.hw_init\", "$@/dhrystone.log", "/dev/null")
	
.PHONY: verilator_taiga_benchmarks
verilator_taiga_benchmarks:
	$(foreach BENCHMARK,$(BENCHMARKS), \
		$(call verilator_local_mem_test,\"$(BENCHMARK_DIR)$(BENCHMARK).riscv.hw_init\", $@/$(BENCHMARK).log, "/dev/null") \
	)

.PHONY: verilator_taiga_embench
verilator_taiga_embench:
	$(foreach BENCHMARK,$(EMBENCH_BENCHMARKS), \
		cd $(EMBENCH_DIR)/$(BENCHMARK); \
		$(ELF_TO_HW_INIT) $(BENCHMARK) $(BENCHMARK).hw_init $(BENCHMARK).sim_init; \
		cd $(TAIGA_DIR)/tools; \
		$(call verilator_local_mem_test,\"$(EMBENCH_DIR)/$(BENCHMARK)/$(BENCHMARK).hw_init\", $@/$(BENCHMARK).log, "/dev/null"); \
	)

#Called by compliance makefile
.PHONY: verilator_taiga_compliance_unit_test
verilator_taiga_compliance_unit_test:
	$(call verilator_local_mem_test,\"$(COMPLIANCE_BENCHAMRK)\", $(LOG_FILE_NAME), $(SIG_FILE_NAME))

.PHONY: verilator_taiga_compliance_tests
verilator_taiga_compliance_tests:
	$(MAKE) -C $(COMPLIANCE_DIR) clean
	$(MAKE) -C $(COMPLIANCE_DIR) RISCV_TARGET=taiga RISCV_DEVICE=$(COMPLIANCE_TARGET) RISCV_PREFIX=$(RISCV_PREFIX) TAIGA_ROOT=$(TAIGA_DIR)/tools

.PHONY: verilator_taiga_coremark
verilator_taiga_coremark:
	$(MAKE) -C  $(COREMARK_DIR) compile PORT_DIR=taiga-sim ITERATIONS=5000;
	cd $(MAKEFILE_DIR);
	$(ELF_TO_HW_INIT) $(COREMARK_DIR)/coremark.bin coremark.hw_init coremark.sim_init
	$(call verilator_local_mem_test,\"coremark.hw_init\", "coremark.log", "coremark.sig")
	
clean:
	rm -rf ./verilator_taiga_dhrystone
	rm -rf ./verilator_taiga_benchmarks
	rm -rf ./verilator_taiga_compliance_unit_test
	rm -rf ./verilator_taiga_coremark
	
