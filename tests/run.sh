#!/bin/bash
opt -load RangeAnalysis.so -load SRAA.so -sraa  -stats $2 $1.essa.bc
