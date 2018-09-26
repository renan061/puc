#
# Makefile
#

CC := gcc-7 
CFLAGS := -Wall

main:
	@- $(CC) $(CFLAGS) -c main.c -o main.o
	@- $(CC) $(CFLAGS) main.o -o broadcast

run: clean main
	@- # ./broadcast <producers> <consumers>
	@- ./broadcast 3 3

clean:
	@- rm -f *.o
	@- rm -f broadcast
