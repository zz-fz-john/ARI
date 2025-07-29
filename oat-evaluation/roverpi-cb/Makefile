# I guess that requiring people to instal Scons is silly, so I'll add this
# Makefile.

OPT = /home/zrz0517/study/chain_attestation/ARI-zrz/conattestllvm/build/bin/opt
VM = /your/server/ip:~/work/ra-project/evaluation/roverpi-cb/

NOVA_PATH = ~/work/llvm-env/build/lib/
LLC_ARM =  /home/zrz0517/study/chain_attestation/ARI-zrz/conattestllvm/build/bin/llc
RPI3_GCC_CONFIG = -I~/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf -mfloat-abi=hard -O0 -g -gdwarf-5 -fverbose-asm
RPI3_GCC_CONFIG += -Wall
RPI3_LLC_CONFIG = -float-abi=hard -filetype=obj 
# RPI3_LLC_CONFIG = -float-abi=hard
RPI3_LLC_CONFIG_ASM = -float-abi=hard
TRAMPOLINE_GCC_CONFIG = -mfloat-abi=hard -O0 -fPIC -g -c -Wall
FILE=insPi.sh
TARGET = --target=arm-linux-gnueabihf
GCC = ../../gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/bin/arm-linux-gnueabihf-gcc
TEEC_EXPORT ?=../../optee_client-master/out/export
TA ?= /home/zrz0517/study/chain_attestation/ARI-zrz/lcu14_optee_hello_world-master/ta
RESERVE_R8 = -ffixed-r8
LDADD += -lteec -L$(TEEC_EXPORT)/lib/ -I$(TEEC_EXPORT)/include -mfloat-abi=hard -O0 -g -c -gdwarf-5 -fPIC
TRAMPOLINE_PATH =../../trampoline_lib
SYSROOT=/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc
ta_trampoline:
	$(GCC) $(LDADD)   $(TRAMPOLINE_PATH)/ta_trampoline.c -o $(TRAMPOLINE_PATH)/ta_trampoline.o -lc
trampoline:
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/trampoline_fw.S -o $(TRAMPOLINE_PATH)/trampoline_fw.o
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/shared_data_sections.S -o $(TRAMPOLINE_PATH)/shared_data_sections.o
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/trampoline.S -o $(TRAMPOLINE_PATH)/trampoline.o
cit_checking_obj:
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(RESERVE_R8) $(TRAMPOLINE_PATH)/ict_checking.c -o $(TRAMPOLINE_PATH)/ict_checking.o
util:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) -S -emit-llvm util.c -o util.bc
tcp: 
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG)  --sysroot=$(SYSROOT) \
	--gcc-toolchain=~/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf \
	tcp.c -S -emit-llvm -o tcp.bc 


rovertcp:
	#clang -D_GNU_SOURCE --target=aarch64 -S -emit-llvm light-controller.c -o light-controller.bc
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) -S -emit-llvm  rovertcp.c -o rovertcp.bc

test-combo: tcp rovertcp trampoline cit_checking_obj ta_trampoline util
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/llvm-link util.bc tcp.bc rovertcp.bc -o test_combo.bc

opt-combo:
	$(OPT) -load $(NOVA_PATH)/LLVMNova.so -nova < test_combo.bc > combo.bc 2>err.log
	$(OPT) -load $(NOVA_PATH)/LLVMCollectCFVHints.so -collect-ibranch-hints-pass -collect-icall-hints-pass -collect-cond-branch-hints-pass < combo.bc > combo_hints.bc 2>>err.log
	$(LLC_ARM) -march=aarch64  -aarch64-enable-cfv combo_hints.bc -o combo.s

client: client.c
	clang client.c -o client

send-combo-bc:
	scp -i vm test_combo.bc $(VM)

fetch-combo-s:
	scp $(VM)/combo.s . 

fetch-file:
	scp $(VM)/$(FILE) . 

bin: test-combo
	clang combo.s -L../../data/runtime -lm $(LDLIBS) -lrt  -lsoftboundcets_rt  -lnova -lteec -lc -lwiringPi 

.PHONY:	clean
clean:
	rm -f *.o
