# A LaTeX/MetaPost makefile for CPSA documents

# Requrements
# * GNU Make
# * package texlive-context
# * package texlive-pictures

# See README for more information

SHELL = /bin/sh

PRIMER = cpsaprimer
OVERVIEW = cpsaoverview
SLIDES = cpsaintroslides
DESIGN = cpsadesign
SPEC = cpsaspec
BIB = cpsa

TEX_SRCS = macros.tex bcasyntax.tex

MP_SRCS	= cpsadiagrams.mp carriers.mp termtree.mp blanchet.mp mitrelogo.mp

%-0.mps:	%.mp
	mpost -tex=latex $*

%.bbl:	$(BIB).bib
	if test ! -f $*.aux; then pdflatex $*.tex; fi
	bibtex $*
	pdflatex $*.tex

%.ind:	%.idx
	makeindex $*

all:	$(PRIMER).pdf $(OVERVIEW).pdf $(SLIDES).pdf \
		$(DESIGN).pdf $(SPEC).pdf

$(PRIMER).pdf:	$(MP_SRCS:.mp=-0.mps) $(TEX_SRCS) \
		 $(PRIMER).tex $(PRIMER).bbl
	if test ! -f $(PRIMER).aux; then pdflatex $(PRIMER).tex; fi
	if test -f $(PRIMER).idx; then $(MAKE) $(PRIMER).ind; fi
	pdflatex $(PRIMER).tex

$(OVERVIEW).pdf: $(OVERVIEW).tex $(OVERVIEW).bbl
	if test ! -f $(OVERVIEW).aux; then pdflatex $(OVERVIEW).tex; fi
	pdflatex $(OVERVIEW).tex

$(SLIDES).pdf:	$(MP_SRCS:.mp=-0.mps) $(SLIDES).tex
	pdflatex $(SLIDES).tex

$(DESIGN).pdf:	$(MP_SRCS:.mp=-0.mps) $(TEX_SRCS) \
		 $(DESIGN).tex $(DESIGN).bbl
	if test ! -f $(DESIGN).aux; then pdflatex $(DESIGN).tex; fi
	if test -f $(DESIGN).idx; then $(MAKE) $(DESIGN).ind; fi
	pdflatex $(DESIGN).tex

$(SPEC).pdf:	$(MP_SRCS:.mp=-0.mps) $(TEX_SRCS) \
		 $(SPEC).tex $(SPEC).bbl
	if test ! -f $(SPEC).aux; then pdflatex $(SPEC).tex; fi
	if test -f $(SPEC).idx; then $(MAKE) $(SPEC).ind; fi
	pdflatex $(SPEC).tex

CLEAN_FILES := $(PRIMER).pdf $(OVERVIEW).pdf $(SLIDES).pdf \
		$(DESIGN).pdf $(SPEC).pdf \
	$(wildcard *.log *.aux *.toc *.mps *.mpx) \
	$(wildcard *.bbl *.blg *.ind *.idx *.ilg *.out)

clean:
	-rm $(CLEAN_FILES)

dist:	clean
	DIR=`pwd`; DIR=`basename $${DIR}`; \
	cd ..; tar czf $${DIR}.tar.gz $${DIR}
