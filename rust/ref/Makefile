CC=clang-20
AR=llvm-ar-20
all: tref librefc.a

#gcc -c -O3 -Wall -fopt-info-vec-missed poly.c

poly.o: poly.c poly.h
	$(CC) -c -O3 -Wall poly.c

tref.o: tref.c poly.h
	$(CC) -c -O0 -Wall -I$(HOME)/include tref.c

tref: tref.o poly.o
	$(CC) -o tref tref.o poly.o -lcpucycles -L$(HOME)/lib

librefc.a: poly.o
	$(AR) r librefc.a poly.o
	cp librefc.a $(HOME)/lib

