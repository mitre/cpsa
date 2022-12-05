TEX_SRCS := $(wildcard *.tex)
LATEX = pdflatex

%.pdf:	%.tex
	$(LATEX) $*
	$(LATEX) $*

all:	$(TEX_SRCS:.tex=.pdf)

clean:
	-rm $(TEX_SRCS:.tex=.pdf) $(TEX_SRCS:.tex=.log) $(TEX_SRCS:.tex=.aux)
