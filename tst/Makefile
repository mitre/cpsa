CPSAFLAGS = +RTS -M1024m -N12 -RTS
CPSATIME = time 

SRCS := $(wildcard *.scm) $(wildcard *.prot) $(wildcard *.lsp)

include ../doc/cpsa4.mk

all:	$(SRCS:%.scm=%_shapes.xhtml) $(SRCS:%.scm=%.xhtml) \
	$(SRCS:%.prot=%_shapes.xhtml) $(SRCS:%.prot=%.xhtml) \
	$(SRCS:%.lsp=%_shapes.xhtml) $(SRCS:%.lsp=%.xhtml)

trim:
	-rm *.xhtml *_shapes* *_sas*

clean:
	-rm *.txt *.xhtml *_shapes* *_sas*
