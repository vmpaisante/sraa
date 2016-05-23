#!/bin/bash
clang -c -emit-llvm $1.c -o $1.bc; 
opt -load vSSA.so -mem2reg -instnamer -break-crit-edges -vssa $1.bc -o $1.essa.bc;
llvm-dis $1.essa.bc -o $1.essa.ll
