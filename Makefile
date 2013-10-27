.PHONY: all clean test

CC ?= gcc
CFLAGS := -O2 ${CFLAGS}

all: test

test: harness.py pan
	./$<

pan: pan.c
	${CC} ${CFLAGS} -o $@ $<

pan.c: hazgas.pml params.pml rooms.pml claims.ltl
	spin -a -L $<

clean:
	rm -rf pan pan.*
