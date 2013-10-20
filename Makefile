.PHONY: all clean test

CC ?= icc
CFLAGS ?= -O2

all: test

test: harness.py pan
	./$<

pan: pan.c
	${CC} ${CFLAGS} -o $@ $<

pan.c: hazgas.pml params.pml rooms.pml claims.ltl
	spin -a -L $<

clean:
	rm -f pan pan.*
