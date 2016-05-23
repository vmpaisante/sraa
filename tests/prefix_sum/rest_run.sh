#!/bin/bash

# This script tests Pericles' version of restrictification against the default
# optimizations present in LLVM -O3.
# Usage: ./run.sh

export LLVM_LIB="/home/pericles/lge/nike/build-debug"
export LLVM_PATH="/home/pericles/lge/build-debug/bin"
export CLANG="$LLVM_PATH/clang"
export OPT="$LLVM_PATH/opt"
export LINKER="$LLVM_PATH/llvm-link"
export DIS="$LLVM_PATH/llvm-dis"

$CLANG -c -emit-llvm -g utils.c -o utils.bc
$CLANG -c -emit-llvm -g prefix_sum.c -o prefix_sum.bc
$CLANG -c -emit-llvm -g prefix_sum_main.c -o main.bc
$LINKER *.bc -o prefix_sum.bc

# Compile the program without restrictification using -O0
$OPT prefix_sum.bc -o prefix_sum.rbc
$DIS prefix_sum.rbc -o prefix_sum.ll
$CLANG prefix_sum.ll -o prefix_sum.exe
echo "[-O0]:"
./prefix_sum.exe 10000 1

# Compile the program without restrictification using -O1
$OPT -O1 prefix_sum.bc -o prefix_sum.rbc
$DIS prefix_sum.rbc -o prefix_sum.ll
$CLANG prefix_sum.ll -o prefix_sum.exe
echo "[-O1]:"
./prefix_sum.exe 10000 1

# Compile the program without restrictification using -O2
$OPT -O2 prefix_sum.bc -o prefix_sum.rbc
$DIS prefix_sum.rbc -o prefix_sum.ll
$CLANG prefix_sum.ll -o prefix_sum.exe
echo "[-O2]:"
./prefix_sum.exe 10000 1

# Compile the program without restrictification using -O3
$OPT -O3 prefix_sum.bc -o prefix_sum.rbc
$DIS prefix_sum.rbc -o prefix_sum.ll
$CLANG prefix_sum.ll -o prefix_sum.exe
echo "[-O3]:"
./prefix_sum.exe 10000 1

# Using Pericles' optimization
$OPT -O3 -load $LLVM_LIB/PtrRangeAnalysis/libLLVMPtrRangeAnalysis.so -load $LLVM_LIB/AliasInstrumentation/libLLVMAliasInstrumentation.so  -ptr-ra -function-alias-checks prefix_sum.bc -o prefix_sum.rbc
$DIS prefix_sum.rbc -o prefix_sum.ll
$CLANG prefix_sum.ll -o prefix_sum.exe
echo "[Restrictifiction]:"
./prefix_sum.exe 10000 1

rm -rf *.bc *.rbc *.ll *.exe
