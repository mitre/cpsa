# A LaTeX/MetaPost makefile for CPSA documents

# Requrements
# * GNU Make
# * package texlive-context
# * package texlive-pictures

# See README for more information

SHELL = /bin/sh

PRIMER = cpsaprimer
GOALS = cpsagoals
SLIDES = cpsaintroslides
DESIGN = cpsadesign
SPEC = cpsaspec
FOUNDATION = cpsafoundation
ANALYZE = cpsaanalyze
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

all:	$(PRIMER).pdf $(GOALS).pdf $(SLIDES).pdf $(DESIGN).pdf\
	$(SPEC).pdf $(FOUNDATION).pdf $(ANALYZE).pdf

$(PRIMER).pdf:	$(MP_SRCS:.mp=-0.mps) $(TEX_SRCS) \
		 $(PRIMER).tex $(PRIMER).bbl
	if test ! -f $(PRIMER).aux; then pdflatex $(PRIMER).tex; fi
	if test -f $(PRIMER).idx; then $(MAKE) $(PRIMER).ind; fi
	pdflatex $(PRIMER).tex

$(GOALS).pdf: $(MP_SRCS:.mp=-0.mps) $(TEX_SRCS) \
		$(GOALS).tex $(GOALS).bbl
	if test ! -f $(GOALS).aux; then pdflatex $(GOALS).tex; fi
	pdflatex $(GOALS).tex

$(FOUNDATION).pdf: $(MP_SRCS:.mp=-0.mps) $(TEX_SRCS) \
		$(FOUNDATION).tex $(FOUNDATION).bbl
	if test ! -f $(FOUNDATION).aux; then pdflatex $(FOUNDATION).tex; fi
	pdflatex $(FOUNDATION).tex

$(ANALYZE).pdf: $(MP_SRCS:.mp=-0.mps) $(TEX_SRCS) \
		$(ANALYZE).tex $(ANALYZE).bbl
	if test ! -f $(ANALYZE).aux; then pdflatex $(ANALYZE).tex; fi
	pdflatex $(ANALYZE).tex

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

CLEAN_FILES := $(PRIMER).pdf $(GOALS).pdf $(SLIDES).pdf \
               $(DESIGN).pdf $(SPEC).pdf $(FOUNDATION).pdf \
               $(ANALYZE).pdf \
	$(wildcard *.log *.aux *.toc *.mps *.mpx *.lot *.lof) \
	$(wildcard *.bbl *.blg *.ind *.idx *.ilg *.out)

clean:
	-rm $(CLEAN_FILES)

dist:	clean
	DIR=`pwd`; DIR=`basename $${DIR}`; \
	cd ..; tar czf $${DIR}.tar.gz $${DIR}
