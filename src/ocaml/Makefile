OCFLAGS	= -classic-display
OCB	= ocamlbuild
SRCS	= $(wildcard *.ml *.mli *.mly *.mll)
TARGETS	= cpsa.top

all:	$(TARGETS)

$(TARGETS):	$(SRCS)
	for i in $(notdir $(TARGETS)); do $(OCB) $(OCFLAGS) "$$i"; done

clean:
	$(OCB) $(OCFLAGS) -clean
