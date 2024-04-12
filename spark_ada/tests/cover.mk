HOSTOS := $(shell uname -s)

all: cleanall diff cover_results

diff: new.txt ../../KAT/MLKEM/kat_MLKEM_768.rsp
	@echo "--- Diffing result - blank response means success  ---"
	-diff $^

new.txt: tkats
	@echo "--- Running tkats ---"
	./tkats -f >$@

cover_results: new.txt
	gcov tkats.adb
	cd ../obj; gcov mlkem.adb

tkats: tkats.gpr tkats.adb ../lib/libmlkem.a
	@echo "--- Building tkats ---"
	gprbuild -Ptkats -XMLKEM_HOSTOS=$(HOSTOS) -XMLKEM_COVERAGE=enabled

../lib/libmlkem.a: ../src/*.ads ../src/*.adb ../libkeccak/lib/generic_none/libkeccak.a
	@echo "--- Building LibMLKEM ---"
	cd ..; gprbuild -Pmlkem -XMLKEM_COVERAGE=enabled -XMLKEM_BUILD_MODE=debug -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled

../libkeccak/lib/generic_none/libkeccak.a: ../libkeccak/src/common/*.ads ../libkeccak/src/common/*.adb
	@echo "--- Building libkeccak ---"
	cd ../libkeccak; alr build

clean:
	gprclean -Ptkats

cleanall: clean
	cd ..; gprclean -Pmlkem
