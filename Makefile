.PHONY: all clean

CC ?= icc

all: pan

pan: pan.c
	${CC} -O2 -o $@ $<

pan.c: hazgas.pml params.pml rooms.pml claims.ltl
	spin -a -L $<

clean:
	rm -f pan pan.*
