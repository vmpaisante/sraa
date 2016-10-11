##======- Makefile --------------------------------------*- Makefile -*-======##
##===----------------------------------------------------------------------===##
PROJECT_NAME = SRAA
LIBRARYNAME = SRAA
LOADABLE_MODULE = 1
USEDLIBS =
LEVEL = .
LLVM_SRC_ROOT = /home/juniocezar/Applications/a-llvm37/llvm-3.7.1.src
LLVM_OBJ_ROOT = /home/juniocezar/Applications/a-llvm37/llvm-3.7.1.src/build
PROJ_SRC_ROOT = .
PROJ_OBJ_ROOT = .
PROJ_INSTALL_ROOT = /home/juniocezar/Applications/a-llvm37/llvm-3.7.1.src/build/Debug+Asserts/lib/..
include $(LLVM_OBJ_ROOT)/Makefile.config
include $(LLVM_SRC_ROOT)/Makefile.rules
cp:
	cp Debug+Asserts/lib/SRAA.so $(PROJ_INSTALL_ROOT)/lib -v
