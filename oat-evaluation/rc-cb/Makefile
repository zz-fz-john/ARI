# I guess that requiring people to instal Scons is silly, so I'll add this
# Makefile.

OPT = /home/zrz0517/study/chain_attestation/ARI-zrz/conattestllvm/build/bin/opt
VM = your-server-for-llvm:~/work/ra-project/evaluation/rc-cb/

NOVA_PATH = ~/work/llvm-env/build/lib/
LLC_ARM = /home/zrz0517/study/chain_attestation/ARI-zrz/conattestllvm/build/bin/llc
RPI3_GCC_CONFIG = -I~/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf -mfloat-abi=hard -O0 -g -gdwarf-5 -fverbose-asm
RPI3_GCC_CONFIG += -Wall
RPI3_LLC_CONFIG = -float-abi=hard -filetype=obj 
RPI3_LLC_CONFIG_ASM = -float-abi=hard
TRAMPOLINE_GCC_CONFIG = -mfloat-abi=hard -O0 -fPIC -g -c -Wall
GCC = ../../gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/bin/arm-linux-gnueabihf-gcc
TEEC_EXPORT ?=../../optee_client-master/out/export
TA ?= /home/zrz0517/study/chain_attestation/ARI-zrz/lcu14_optee_hello_world-master/ta
RESERVE_R8 = -ffixed-r8
LDADD += -lteec -L$(TEEC_EXPORT)/lib/ -I$(TEEC_EXPORT)/include -mfloat-abi=hard -O0 -g -c -gdwarf-5 -fPIC
TRAMPOLINE_PATH =../../trampoline_lib
SYSROOT=/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc
UNAME := $(shell uname -m)
WARNING_FLAGS := -Wall -Wextra -Wshadow -Wswitch-enum \
    -Wswitch-default
C_WARNING_FLAGS := -Wmissing-prototypes -Wmissing-declarations \
    -Wstrict-prototypes
TARGET = --target=arm-linux-gnueabihf

ifeq ($(UNAME), armv6l)
	CFLAGS := ${WARNING_FLAGS} ${C_WARNING_FLAGS} -DRASPI=1
else ifeq ($(UNAME), armv7l)
	CFLAGS := ${WARNING_FLAGS} ${C_WARNING_FLAGS} -DRASPI=2
else
	CFLAGS := ${WARNING_FLAGS} ${C_WARNING_FLAGS}
endif

LDLIBS := -lm -ljansson
ta_trampoline:
	$(GCC) $(LDADD)   $(TRAMPOLINE_PATH)/ta_trampoline.c -o $(TRAMPOLINE_PATH)/ta_trampoline.o -lc
trampoline:
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/trampoline_fw.S -o $(TRAMPOLINE_PATH)/trampoline_fw.o
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/shared_data_sections.S -o $(TRAMPOLINE_PATH)/shared_data_sections.o
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/trampoline.S -o $(TRAMPOLINE_PATH)/trampoline.o
cit_checking_obj:
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(RESERVE_R8) $(TRAMPOLINE_PATH)/ict_checking.c -o $(TRAMPOLINE_PATH)/ict_checking.o


dtoa_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/dtoa.c  -o ./dtoa.bc
dump_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/dump.c  -o ./dump.bc
error_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/error.c  -o ./error.bc
hashtable_seed_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/hashtable_seed.c  -o ./hashtable_seed.bc
hashtable_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/hashtable.c  -o ./hashtable.bc
load_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/load.c  -o ./load.bc
memory_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/memory.c  -o ./memory.bc
pack_unpack_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/pack_unpack.c  -o ./pack_unpack.bc
strbuffer_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/strbuffer.c  -o ./strbuffer.bc
strconv_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/strconv.c  -o ./strconv.bc
utf_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/utf.c  -o ./utf.bc
value_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/value.c  -o ./value.bc
version_bc:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm  ./jansson/version.c  -o ./version.bc
jansson_bc: dtoa_bc dump_bc error_bc hashtable_seed_bc hashtable_bc load_bc memory_bc pack_unpack_bc strbuffer_bc strconv_bc utf_bc value_bc version_bc
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/llvm-link dtoa.bc dump.bc error.bc hashtable_seed.bc hashtable.bc load.bc memory.bc pack_unpack.bc strbuffer.bc strconv.bc utf.bc value.bc version.bc -o jansson.bc
pi_pcm: 
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(CFLAGS) $(LDLIBS) pi_pcm.c -o server

pi-pcm-bc:
	#clang -D_GNU_SOURCE --target=aarch64 -S -emit-llvm pi_pcm.c -o pi_pcm.bc
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG)  --sysroot=$(SYSROOT) -I/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/rc-cb/jansson -S -emit-llvm  pi_pcm.c -o pi_pcm.bc
util:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) -S -emit-llvm util.c -o util.bc
test-combo: pi-pcm-bc ta_trampoline trampoline cit_checking_obj jansson_bc util 
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/llvm-link pi_pcm.bc jansson.bc util.bc -o test_combo.bc


opt-combo:
	$(OPT) -load $(NOVA_PATH)/LLVMNova.so -nova < test_combo.bc > combo.bc 2>err.log
	$(OPT) -load $(NOVA_PATH)/LLVMCollectCFVHints.so -collect-ibranch-hints-pass -collect-icall-hints-pass -collect-cond-branch-hints-pass < combo.bc > combo_hints.bc 2>>err.log
	$(LLC_ARM) -march=aarch64  -aarch64-enable-cfv combo_hints.bc -o combo.s


send-combo-bc:
	scp -i vm test_combo.bc $(VM)

fetch-combo-s:
	scp $(VM)/combo.s . 

bin: test-combo
	clang combo.s -L../../data/runtime -lm -ljansson -lrt  -lsoftboundcets_rt  -lnova -lteec -lc 

run-client: 
	./interactive_control.py example.json 
	
run-server: pi_pcm
	./server

sync:
	cp pi_pcm.c Makefile interactive_control.py ~/tee_workspace/ra-project/evaluation/rc-cb/ 

.PHONY:	clean
clean:
	rm -f *.o
	rm -f *.pyc
	rm -f pi_pcm

