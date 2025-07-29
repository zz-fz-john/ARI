TEST ?= test_combo
#CC = aarch64-linux-gnu-gcc
CC = gcc
NUC_PC ?= your-pc-ip 
NUC_TARGET ?= ~/work/ra-project/evaluation/alarm4pi/
objdump ?= aarch64-linux-gnu-objdump 
hikey ?= your-hikey-board-ip 
# TEEC_EXPORT ?= /home/linaro/work/tee/export
TA ?= /home/zrz0517/study/chain_attestation/ARI-zrz/lcu14_optee_hello_world-master/ta
hikey_target ?= ~/work/alarm4pi/

NOVA_PATH = ~/work/llvm-env/build/lib/
# LLC_ARM = ~/work/llvm-env/buildc/bin/llc
LLC_ARM = /home/zrz0517/study/chain_attestation/ARI-zrz/conattestllvm/build/bin/llc

TEEC_EXPORT ?=/home/zrz0517/study/chain_attestation/ARI-zrz/optee_client-master/out/export/

CFLAGS += -Wall -I$(TA)/include -I$(TEEC_EXPORT)/include -I./include
#Add/link other required libraries here
# LDADD += -lteec -L$(TEEC_EXPORT)/lib -lresolv -pthread
LDADD += -lteec -L$(TEEC_EXPORT)/lib/ -I$(TEEC_EXPORT)/include -mfloat-abi=hard -O0 -g -c -gdwarf-5 -fPIC

LDADD_ORIG += -lresolv -pthread
OPT = /home/zrz0517/study/chain_attestation/ARI-zrz/conattestllvm/build/bin/opt
VM = your-server-for-llvm:~/work/ra-project/evaluation/alarm4pi-cb/

TARGET = --target=arm-linux-gnueabihf

RPI3_GCC_CONFIG_ORG = -I/media/rpi/usr/include/arm-linux-gnueabihf -mfloat-abi=hard -O0 -g -gdwarf-2
RPI3_GCC_CONFIG = -I~/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf -mfloat-abi=hard -O0 -g -gdwarf-5 -fverbose-asm
RPI3_GCC_CONFIG += -Wall
RPI3_LLC_CONFIG = -float-abi=hard -filetype=obj 
RPI3_LLC_CONFIG_ASM = -float-abi=hard
TRAMPOLINE_GCC_CONFIG = -mfloat-abi=hard -O0 -fPIC -g -c -Wall
GCC = ../../gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/bin/arm-linux-gnueabihf-gcc
RESERVE_R8 = -ffixed-r8
TRAMPOLINE_PATH =../../trampoline_lib
SYSROOT=/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc
ta_trampoline:
	$(GCC) $(LDADD)  $(TRAMPOLINE_PATH)/ta_trampoline.c -o $(TRAMPOLINE_PATH)/ta_trampoline.o -lc
trampoline:
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/trampoline_fw.S -o $(TRAMPOLINE_PATH)/trampoline_fw.o
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/shared_data_sections.S -o $(TRAMPOLINE_PATH)/shared_data_sections.o
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(TRAMPOLINE_PATH)/trampoline.S -o $(TRAMPOLINE_PATH)/trampoline.o
cit_checking_obj:
	$(GCC) $(TRAMPOLINE_GCC_CONFIG) $(RESERVE_R8) $(TRAMPOLINE_PATH)/ict_checking.c -o $(TRAMPOLINE_PATH)/ict_checking.o

util:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm util.c -o util.bc

bcm-gpio:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm bcm_gpio.c -o bcm_gpio.bc

alarm4pi:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm alarm4pi.c -o alarm4pi.bc

log-msgs:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm log_msgs.c -o log_msgs.bc

proc-helper:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG)  --sysroot=$(SYSROOT) -S -emit-llvm proc_helper.c -o proc_helper.bc

public-ip:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG)  --sysroot=$(SYSROOT) -S -emit-llvm  -lresolv public_ip.c -o public_ip.bc

pushover:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm pushover.c -o pushover.bc

gpio-polling:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) --sysroot=$(SYSROOT) -S -emit-llvm gpio_polling.c -o gpio_polling.bc

gpio-polling-orig:
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang $(TARGET) $(RPI3_GCC_CONFIG) -S -emit-llvm gpio_polling_orig.c -o gpio_polling_orig.bc

test-orig: util alarm4pi gpio-polling-orig pushover public-ip proc-helper log-msgs bcm-gpio
	$(CC) $(LDADD_ORIG) -g util.o alarm4pi.o gpio_polling_orig.o pushover.o public_ip.o proc_helper.o log_msgs.o bcm_gpio.o  -o test_orig
	
test-combo: util alarm4pi gpio-polling pushover public-ip proc-helper log-msgs bcm-gpio  ta_trampoline trampoline cit_checking_obj
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/llvm-link util.bc alarm4pi.bc gpio_polling.bc pushover.bc public_ip.bc proc_helper.bc log_msgs.bc bcm_gpio.bc -o test_combo.bc 

llc-comp:
	$(LLC_ARM)  $(RPI3_LLC_CONFIG) after_compartment_test_combo.bc -o after_comp_combo.s

opt-combo:
	$(OPT) -load $(NOVA_PATH)/LLVMNova.so -nova < test_combo.bc > combo.bc 2>err.log
	$(OPT) -load $(NOVA_PATH)/LLVMCollectCFVHints.so -collect-ibranch-hints-pass -collect-icall-hints-pass -collect-cond-branch-hints-pass < combo.bc > combo_hints.bc 2>>err.log
	$(LLC_ARM) -march=aarch64  -aarch64-enable-cfv combo_hints.bc -o combo.s

send-combo-s:
	scp combo.s machine-name:~/tmp/hikey-relay/

send-combo-bc:
	scp -i vm test_combo.bc $(VM)

fetch-combo-s:
	scp $(VM)/combo.s . 

bin: test-combo
	#clang combo.s -L../../data/runtime -lm -lrt  -lsoftboundcets_rt  -lnova -lteec -lpthread  -lc -lresolv
	clang combo.s -L../../data/runtime -lm -lrt  -lnova -lteec -lpthread  -lc -lresolv

dis-combo:
	llvm-dis < test_combo.bc >test_combo.dis

send-combo:
	scp -i pi $(TEST) $(NUC_PC):~/work/ra-project/evaluation/hook-a64/

send-hikey:
	scp $(TEST) $(hikey):$(hikey_target)

sync-hikey:
	scp -r *.c *.h hooks_a64.S *.ld Makefile lib/ $(hikey):$(hikey_target)

sync-nuc:
	scp -i pi -r *.c *.h hooks_a64.S *.ld Makefile lib/ $(NUC_PC):$(NUC_TARGET)

clean:
	rm *.o
	rm test

dump:
	$(objdump) $(TEST) -D > $(TEST).dump

ph:
	readelf -S  $(TEST)

sh:
	readelf -l  $(TEST)

# Compile Note: cdefs.h not found can be solved by the following cmd
#time CPATH=/usr/include/aarch64-linux-gnu/ make test-combo
