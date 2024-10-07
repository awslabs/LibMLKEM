all: clean tref

tref: tref.adb rmerge2.ads rmerge2.adb rmerge2-inv.ads rmerge2-inv.adb ntt.o
	gprbuild -Ptref

ntt.o: ntt.h ntt.c
	gcc -c ntt.c

clean:
	rm -f ntt.o
	gprclean -Ptref

proof:
	gnatprove -Ptref -u rmerge2-inv.adb
