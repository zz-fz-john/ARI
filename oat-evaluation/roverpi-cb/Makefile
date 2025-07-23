# I guess that requiring people to instal Scons is silly, so I'll add this
# Makefile.

OPT = ~/work/llvm-env/build/bin/opt
VM = /your/server/ip:~/work/ra-project/evaluation/roverpi-cb/

NOVA_PATH = ~/work/llvm-env/build/lib/
LLC_ARM = ~/work/llvm-env/build/bin/llc

FILE=insPi.sh

tcp: 
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang tcp.c -S -emit-llvm -o tcp.bc

rovertcp:
	#clang -D_GNU_SOURCE --target=aarch64 -S -emit-llvm light-controller.c -o light-controller.bc
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang -S -emit-llvm  rovertcp.c -o rovertcp.bc

test-combo: tcp rovertcp 
	/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/llvm-link  tcp.bc rovertcp.bc -o test_combo.bc

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
