.PHONY: run_dhrystone_verilator
run_dhrystone_verilator :
	$(call verilator_local_mem_test,dhrystone,/home/ematthew/Research/RISCV/software/taiga-benchmarks/dhrystone.riscv.hw_init,"/dev/null","/dev/null")

.PHONY: build_embench
build_embench :
	cd $(EMBENCH_DIR);\
	rm -rf build;\
	mkdir build;\
	cd build;\
	../configure --host=riscv32-unknown-elf --with-chip=speed-test --with-board=taiga-sim;\
	make

