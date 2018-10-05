#
# Makefile
#

CC := clang
CPPC := clang++

CFLAGS := `llvm-config --cflags` -Wall
CPPFLAGS := ` llvm-config --cxxflags --ldflags --system-libs`
CPPFLAGS += ` llvm-config --libs core bitreader bitwriter`

main:
	@- $(CC) $(CFLAGS) -c main.c -o main.o
	@- $(CPPC) $(CPPFLAGS) main.o -o main

run: clean main
	@- llvm-as ir/input.ll -o input.ll
	@- ./main input.bc output.bc

clean:
	@- rm -f *.o
	@- rm -f input.bc
	@- rm -f output.bc
	@- rm -f main
