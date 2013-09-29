SPIN ?= spin

.PHONY: all

all: hazgas.pml
	${SPIN} $<
