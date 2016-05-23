#!/bin/bash
opt -load RangeAnalysis.so -load SRAA.so -sraa -aa-eval -stats -print-all-alias-modref-info -debug $1.essa.bc
