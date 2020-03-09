CPSAFLAGS = +RTS -M512m -N -RTS
CPSAPROTFLAGS = -e

SRCS := $(wildcard *.prot)

include ../cpsa4.mk

all:	$(SRCS:%.prot=%_shapes.xhtml) $(SRCS:%.prot=%.xhtml)

clean:
	-rm *.txt *.xhtml
