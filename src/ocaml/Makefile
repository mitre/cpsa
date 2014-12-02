OCFLAGS	= -classic-display
OCB	= ocamlbuild
SRCS	= $(wildcard *.ml *.mli *.mly *.mll)
TARGETS	= cpsa.top

all:	$(TARGETS)

$(TARGETS):	$(SRCS)
	$(OCB) $(OCFLAGS) $(notdir $@)

clean:
	$(OCB) $(OCFLAGS) -clean
