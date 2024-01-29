all: sizes.txt

sizes.txt: src/*.ads src/*.adb
	echo "MLKEM -O0" >sizes.txt
	echo "---------" >>sizes.txt
	gprclean -Pmlkem
	gprbuild  -Pmlkem -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled -XMLKEM_BUILD_MODE=debug
	size -m obj/mlkem.o >>sizes.txt
	gnatstack -Pmlkem >>sizes.txt
	echo "MLKEM -O1" >>sizes.txt
	echo "---------" >>sizes.txt
	gprclean -Pmlkem
	gprbuild  -Pmlkem -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled -XMLKEM_BUILD_MODE=O1
	size -m obj/mlkem.o >>sizes.txt
	gnatstack -Pmlkem >>sizes.txt
	echo "MLKEM -O2" >>sizes.txt
	echo "---------" >>sizes.txt
	gprclean -Pmlkem
	gprbuild  -Pmlkem -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled -XMLKEM_BUILD_MODE=O2
	size -m obj/mlkem.o >>sizes.txt
	gnatstack -Pmlkem >>sizes.txt
	echo "MLKEM -O3" >>sizes.txt
	echo "---------" >>sizes.txt
	gprclean -Pmlkem
	gprbuild  -Pmlkem -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled -XMLKEM_BUILD_MODE=O3
	size -m obj/mlkem.o >>sizes.txt
	gnatstack -Pmlkem >>sizes.txt
	echo "MLKEM -Os" >>sizes.txt
	echo "---------" >>sizes.txt
	gprclean -Pmlkem
	gprbuild  -Pmlkem -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled -XMLKEM_BUILD_MODE=Os
	size -m obj/mlkem.o >>sizes.txt
	gnatstack -Pmlkem >>sizes.txt
	gprclean -Pmlkem
