# A LaTeX/MetaPost makefile -- requires GNU Make

# John D. Ramsdell -- The MITRE Corporation

# The makefile assumes all the *.tex and *.mp source files in this
# directory are used to build one document.  You need not have any
# MetaPost source files to use this makefile.

# To use this file, include this file in your Makefile, and define
# BASE_NAME to be the base name of the document to be created.  If you
# use BiBTeX, define BIB_NAME to be the base name of the BiBTeX file.
# Define MP_MACROS to be the name of local MetaPost macro library
# files.

# Example Makefile:

# BASE_NAME = mydoc
# BIB_NAME = mybib
# include ltxmp.mk

# During development, this makefile doesn't always run enough programs
# in response to changes in the source files.  Be sure to precede a
# make with a make clean when you want to build a final version of a
# document.

SHELL = /bin/sh

ifndef BASE_NAME
  BASE_NAME = root
endif

ifndef LATEX
  LATEX = pdflatex
endif

TEX_SRCS := $(wildcard *.tex)

MP_SRCS	:= $(wildcard *.mp)

MP_FIGS := $(filter-out $(MP_MACROS),$(MP_SRCS))

%-0.mps:	%.mp
	mpost -tex=latex $*

all:	$(BASE_NAME).pdf

$(BASE_NAME).pdf:	$(TEX_SRCS) $(MP_FIGS:.mp=-0.mps)
	if test ! -f $(BASE_NAME).aux; then $(LATEX) $(BASE_NAME).tex; fi
	if test -f $(BASE_NAME).idx; then $(MAKE) $(BASE_NAME).ind; fi
	$(LATEX) $(BASE_NAME).tex

ifdef BIB_NAME
  $(BASE_NAME).pdf:	$(BASE_NAME).bbl
endif

$(BASE_NAME).bbl:	$(BIB_NAME).bib
	if test ! -f $(BASE_NAME).aux; then $(LATEX) $(BASE_NAME).tex; fi
	bibtex $(BASE_NAME)
	$(LATEX) $(BASE_NAME).tex

$(BASE_NAME).ind:	$(BASE_NAME).idx
	makeindex $(BASE_NAME)

CLEAN_FILES := $(BASE_NAME).pdf \
	$(wildcard *.log *.aux *.toc *.lof *.out) \
	$(wildcard *.mpx $(patsubst %.mp,%-*.mps,$(MP_FIGS))) \
	$(wildcard *.bbl *.blg *.ind *.idx *.ilg) \
	$(wildcard $(BASE_NAME).dvi $(BASE_NAME).ps)

clean:
	-rm $(CLEAN_FILES)

dist:	clean
	DIR=`pwd`; DIR=`basename $${DIR}`; \
	cd ..; tar czf $${DIR}.tar.gz $${DIR}
