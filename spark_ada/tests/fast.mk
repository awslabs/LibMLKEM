include Makefile.common

../lib/libmlkem.a: ../src/*.ads ../src/*.adb ../libkeccak/lib/generic_none/libkeccak.a
	@echo "--- Building LibMLKEM ---"
	cd ..; gprclean -Pmlkem; gprbuild -Pmlkem -XMLKEM_BUILD_MODE=O3 -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled
