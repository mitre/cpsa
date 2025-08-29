CPSAFLAGS = +RTS -M512m -RTS
GRAPHFLAGS = -p

SRCS := $(wildcard *.scm) $(wildcard *.lsp)

include cpsa4.mk

all:    $(SRCS:%.scm=%_shapes.xhtml) $(SRCS:%.scm=%.xhtml) \
	$(SRCS:%.lsp=%_shapes.xhtml) $(SRCS:%.lsp=%.xhtml)

clean:
	-rm *.txt *.xhtml
