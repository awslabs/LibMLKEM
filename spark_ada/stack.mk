all: stack

stack: src/*.ads src/*.adb
	gprclean -Pmlkem
	gprbuild -Pmlkem -XMLKEM_RUNTIME_TIME=zfp -XMLKEM_RUNTIME_CHECKS=disabled -XMLKEM_CONTRACTS=disabled -XMLKEM_BUILD_MODE=O1
	gnatstack -Pmlkem
