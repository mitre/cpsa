OCFLAGS	= -verbose 0
OCB	= ocamlbuild
SRCS	= $(wildcard *.ml *.mli *.mly *.mll)
TARGETS	= _build/cpsa.cma

all:	$(TARGETS)

$(TARGETS):	$(SRCS)
	for i in $(notdir $(TARGETS)); do $(OCB) $(OCFLAGS) "$$i"; done

clean:
	$(OCB) $(OCFLAGS) -clean
