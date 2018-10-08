#
# Makefile
#

CC := clang
CPPC := clang++

CFLAGS := `llvm-config --cflags` -Wall
CPPFLAGS := ` llvm-config --cxxflags --ldflags --system-libs`
CPPFLAGS += ` llvm-config --libs core bitreader bitwriter`

main: objs
	@- $(CPPC) $(CPPFLAGS) obj/list.o obj/bb.o obj/main.o -o bin/main

objs:
	@- $(CC) $(CFLAGS) -c src/list.c -o obj/list.o
	@- $(CC) $(CFLAGS) -c src/bb.c -o obj/bb.o
	@- $(CC) $(CFLAGS) -c src/main.c -o obj/main.o

run: clean main
	@- # @- ./bin/mongacompiler < input.monga > input.ll
	@- # cat input.ll
	@- # echo =========================
	@- llvm-as input.ll -o input.bc
	@- ./bin/main input.bc output.bc
	@- lli output.bc

clean:
	@- rm -f obj/*.o
	@- rm -f *.bc
	@- rm -f bin/main
