CURRENT_DIR=$(pwd)
ROOT_DIR="${CURRENT_DIR}/.."
TOOLCHAIN_DIR="${ROOT_DIR}/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf"
LLVM_LINK="/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/llvm-link"
./build_all.py \
     --arch=arm \
     --chip=generic \
     --board=generic \
     --cc="/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang" \
     --ld="/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang" \
     --cflags="-O0 -flto  -g -gdwarf-4 -flto -fembed-bitcode -fno-exceptions -fno-jump-tables -fno-inline -emit-llvm -c --target=arm-linux-gnueabihf -mcpu=cortex-a53 -I/usr/arm-linux-gnueabihf/include -mfloat-abi=hard -g0 -gdwarf-4 -v"
#/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang++  support/view_switch_and_log.cpp  -O0 -flto  -g -gdwarf-4 -flto -fembed-bitcode -fno-exceptions -fno-jump-tables -fno-inline -emit-llvm -c --target=arm-linux-gnueabihf -mcpu=cortex-a53 -I../lcu14_optee_hello_world-master/ta/include -I../optee_client-master/out/export/include -I/usr/arm-linux-gnueabihf/include -mfloat-abi=hard -g0 -gdwarf-4 -v -o support/view_switch_and_log.o || exit 1
/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/clang++ \
  support/view_switch_and_log.cpp \
  -std=c++11 \
  -O0  -g -gdwarf-4 -fembed-bitcode -fno-exceptions -fno-jump-tables -fno-inline \
     -c \
  --target=arm-linux-gnueabihf -mcpu=cortex-a53 \
  -I../lcu14_optee_hello_world-master/ta/include \
  -I../optee_client-master/out/export/include \
  -I/usr/arm-linux-gnueabihf/include \
  -I/usr/arm-linux-gnueabihf/include/c++/9/arm-linux-gnueabihf \
  -mfloat-abi=hard -g0 -gdwarf-4 -v \
  -o support/view_switch_and_log.o || exit 1

cp sec_mask_result.txt bd/sec_mask_result.txt
cp crit_cpt.txt bd/crit_cpt.txt
cd bd
rm -f src/"$1"/llvm-link_cond_br.o||exit 1
$LLVM_LINK \
    src/"$1"/*.o \
    support/*.o \
    config/arm/boards/generic/boardsupport.o \
    config/arm/chips/generic/chipsupport.o \
    -o src/"$1"/"$1".bc ||exit 1   
../../conattestllvm/build/bin/llvm-dis src/"$1"/"$1".bc -o src/"$1"/"$1".ll ||exit 1
../../conattestllvm/build/bin/opt -f -load ../conattestllvm/build/lib/LLVMgold.so -HexboxAnaysis --hexbox-analysis-results=./analysis_result.json src/"$1"/"$1".bc > ./src/"$1"/after_hexbox_info_clct.bc ||exit 1


python2 ../../graph_analysis/analyzer.py -j=./analysis_result.json -s=./size_result.json -o=./compartments_result.json  -m=operation -b=STM32F479 -T=../../oat-evaluation/syringe-cb/arm_link_script_syringe.txt -f=../critical_function.txt -L=../arm_link_script_syringe_intermidea.txt ||exit 1

../../conattestllvm/build/bin/opt -f -load ../../conattestllvm/build/lib/LLVMgold.so -HexboxApplication --hexbox-policy=./compartments_result.json src/"$1"/"$1".bc > ./src/"$1"/after_compartment_llvm_link.bc ||exit 1

../../conattestllvm/build/bin/llc -filetype=obj ./src/"$1"/after_compartment_llvm_link.bc -o ./src/"$1"/llvm-link_cond_br.o ||exit 1
cd ..
cd ../oat-evaluation/syringe-cb
make trampoline
make cit_checking_obj

cd ../../embench_test/bd || exit 1

../../gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/bin/ld -T ../arm_link_script_syringe_intermidea.txt  -EL -z relro -X --hash-style=gnu --eh-frame-hdr -m armelf_linux_eabi -dynamic-linker /lib/ld-linux-armhf.so.3 -o ./src/"$1"/"$1"_ARI $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/usr/lib/Scrt1.o $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/usr/lib/crti.o $TOOLCHAIN_DIR/lib/gcc/arm-linux-gnueabihf/6.2.1/crtbeginS.o -L/usr/lib/gcc-cross/arm-linux-gnueabihf/9 -L/usr/lib/gcc-cross/arm-linux-gnueabihf/9/../../../../arm-linux-gnueabihf/lib/../lib -L/usr/lib/gcc-cross/arm-linux-gnueabihf/9/../../../../lib -L/lib/arm-linux-gnueabihf -L/lib/../lib -L/usr/lib/arm-linux-gnueabihf -L/usr/lib/../lib -L/usr/lib/gcc-cross/arm-linux-gnueabihf/9/../../../../arm-linux-gnueabihf/lib -L/lib -L/usr/lib  -Bstatic ./src/"$1"/llvm-link_cond_br.o  ../../trampoline_lib/blake2s ../../trampoline_lib/ict_checking.o ../../trampoline_lib/trampoline_fw.o ../../trampoline_lib/shared_data_sections.o ../../trampoline_lib/trampoline.o ../support/view_switch_and_log.o -Bdynamic $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/lib/libm.so.6 $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/lib/libdl.so.2 $TOOLCHAIN_DIR/arm-linux-gnueabihf/lib/libstdc++.so.6 $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/lib/libm.so.6 $TOOLCHAIN_DIR/arm-linux-gnueabihf/lib/libgcc_s.so.1  $TOOLCHAIN_DIR/lib/gcc/arm-linux-gnueabihf/6.2.1/libgcc.a -lresolv -lpthread -lc $TOOLCHAIN_DIR/arm-linux-gnueabihf/lib/libgcc_s.so.1 $TOOLCHAIN_DIR/lib/gcc/arm-linux-gnueabihf/6.2.1/libgcc.a /usr/lib/gcc-cross/arm-linux-gnueabihf/9/crtendS.o $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/usr/lib/crtn.o ../../optee_client-master/out/export/lib/libteec.a

scp ./src/"$1"/"$1"_ARI pi@192.168.1.101:/home/pi

#../../../gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/bin/ld -T ../../arm_link_script_syringe_intermidea.txt --sysroot=/ -z relro -X --hash-style=gnu --eh-frame-hdr -m armelf_linux_eabi -dynamic-linker /lib/ld-linux-armhf.so.3 -o arducopter43_ARI ../../../trampoline_lib/blake2s ../../../trampoline_lib/ict_checking.o ../../../trampoline_lib/trampoline_fw.o ../../../trampoline_lib/shared_data_sections.o ../../../trampoline_lib/trampoline.o $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/usr/lib/crt1.o $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/usr/lib/crti.o $TOOLCHAIN_DIR/lib/gcc/arm-linux-gnueabihf/6.2.1/crtbegin.o -L/usr/lib/gcc-cross/arm-linux-gnueabihf/9 -L/usr/lib/gcc-cross/arm-linux-gnueabihf/9/../../../../arm-linux-gnueabihf/lib/../lib -L/usr/lib/gcc-cross/arm-linux-gnueabihf/9/../../../../lib -L/home/zrz0517/study/chain_attestation/ARI-zrz/conattestllvm/build/bin/../lib -L/lib/arm-linux-gnueabihf -L/usr/lib/../lib -L/usr/lib/gcc-cross/arm-linux-gnueabihf/9/../../../../arm-linux-gnueabihf/lib -L/lib -L/usr/lib ./llvm-link_cond_br.o -L../../../gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/lib/ $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/lib/libm.so.6 $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/lib/libdl.so.2 $TOOLCHAIN_DIR/arm-linux-gnueabihf/lib/libstdc++.so.6 $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/lib/libm.so.6 $TOOLCHAIN_DIR/arm-linux-gnueabihf/lib/libgcc_s.so.1  $TOOLCHAIN_DIR/lib/gcc/arm-linux-gnueabihf/6.2.1/libgcc.a -lpthread -lc $TOOLCHAIN_DIR/arm-linux-gnueabihf/lib/libgcc_s.so.1 $TOOLCHAIN_DIR/lib/gcc/arm-linux-gnueabihf/6.2.1/libgcc.a /usr/lib/gcc-cross/arm-linux-gnueabihf/9/crtendS.o $TOOLCHAIN_DIR/arm-linux-gnueabihf/libc/usr/lib/crtn.o ../../../optee_client-master/out/export/lib/libteec.a