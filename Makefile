##======- Makefile --------------------------------------*- Makefile -*-======##
##===----------------------------------------------------------------------===##
PROJECT_NAME = SRAA
LIBRARYNAME = SRAA
LOADABLE_MODULE = 1
USEDLIBS =
LEVEL = .
LLVM_SRC_ROOT = /home/junio/llvm/37
LLVM_OBJ_ROOT = /home/junio/llvm/37/build
PROJ_SRC_ROOT = .
PROJ_OBJ_ROOT = .
PROJ_INSTALL_ROOT = /home/junio/llvm/37/build/Debug+Asserts/lib/..
include $(LLVM_OBJ_ROOT)/Makefile.config
include $(LLVM_SRC_ROOT)/Makefile.rules
cp:
	cp Debug+Asserts/lib/SRAA.so $(PROJ_INSTALL_ROOT)/lib -v
