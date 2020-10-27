# Coq project makefile

# Documentation target.  Type "make DOC=all-gal.pdf" to make PDF.
DOC	?= gallinahtml

# File $(PROJ) contains the list of source files.
# See "man coq_makefile" for its format.
PROJ	= _CoqProject

# Generated makefile
COQMK	= coq.mk

all:	$(COQMK)
	$(MAKE) -f $(COQMK)
	$(MAKE) -f $(COQMK) $(DOC)

$(COQMK): $(PROJ)
	coq_makefile -o $(COQMK) -f $(PROJ)

$(PROJ):
	@echo make $@

%:	$(COQMK) force
	$(MAKE) -f $(COQMK) $@

clean:	$(COQMK)
	$(MAKE) -f $(COQMK) clean
	rm $(COQMK) $(COQMK).conf

.PHONY:	all clean force
