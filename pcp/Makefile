#
# Makefile
#

CC := gcc-7 
CFLAGS := -Wall

main:
	@- $(CC) $(CFLAGS) -c main.c -o main.o
	@- $(CC) $(CFLAGS) main.o -o main

run: clean main
	@- ./main 2 3

clean:
	@- rm -f *.o
	@- rm -f main
