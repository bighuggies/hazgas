.PHONY: all clean test

CC ?= gcc
CFLAGS := -O2 ${CFLAGS}
PANFLAGS := ${PANFLAGS}
SPINFLAGS := ${SPINFLAGS}

all: test

test: harness.py pan
	./$< ${PANFLAGS}

pan: pan.c
	${CC} ${CFLAGS} -o $@ $<

pan.c: hazgas.pml params.pml rooms.pml claims.ltl
	spin -a -L ${SPINFLAGS} $<

clean:
	rm -rf pan pan.* *.tmp *.trail
