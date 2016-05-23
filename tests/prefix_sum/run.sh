#!/bin/bash

if [ $# -lt 1 ]
then
    echo "Inform path to LLVM tools, e.g., the folder where is clang and opt"
    echo "- E.g.: ./run.sh /Users/chapolin/llvm/Debug/bin"
    exit 1
else
    export LLVM_PATH=$1
    export CLANG="$LLVM_PATH/clang"
    export OPT="$LLVM_PATH/opt"
    export LINKER="$LLVM_PATH/llvm-link"
    export DIS="$LLVM_PATH/llvm-dis"
    rm -rf *.bc *.rbc *.ll *.exe
    $CLANG -c -emit-llvm -g utils.c -o utils.bc
    $CLANG -c -emit-llvm -g prefix_sum.c -o prefix_sum.bc
    $CLANG -c -emit-llvm -g prefix_sum_main.c -o main.bc
    $LINKER *.bc -o prefix_sum.bc
    # No need to disable inlining for this benchmark:
    $OPT -O3 prefix_sum.bc -o prefix_sum.rbc
    $DIS prefix_sum.rbc -o prefix_sum.ll
    $CLANG prefix_sum.ll -o prefix_sum.exe
    echo "Timing the challenge:"
    ./prefix_sum.exe 100000 1
    echo "Timing the baseline:"
    ./prefix_sum.exe 100000 2
fi

