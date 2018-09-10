OCFLAGS	= -classic-display -use-ocamlfind -cflags "-w +A-4"
OCB	= ocamlbuild
TARGET	= cpsa.otarget

all:	
	$(OCB) $(OCFLAGS) $(TARGET)

clean:
	$(OCB) $(OCFLAGS) -clean

Makefile:
	@echo make $@

%:	force
	$(OCB) $(OCFLAGS) $@

.PHONY:	all clean force
