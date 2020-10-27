include coq.mk.conf

DOC	= procdoc.pdf
VTEXFILES = $(COQMF_VFILES:.v=.v.tex)
TEXFILES = $(DOC:.pdf=.tex) body.tex $(VTEXFILES)
COQDOCFLAGS = --interpolate --latex --gallina --body-only --lib-name ""

%.v.tex: %.v
	coqdoc -o $@ $(COQDOCFLAGS) $<

all:	$(DOC)

body.tex:	$(VTEXFILES) _CoqProject
	-rm body.tex
	for i in $(COQMF_VFILES); do echo "\\include{$$i}" >> body.tex; done

$(DOC):	$(TEXFILES)
	pdflatex $(DOC:.pdf=)
	pdflatex $(DOC:.pdf=)

clean:
	-rm body.tex $(VTEXFILES) $(VTEXFILES:.tex=.aux) coqdoc.sty
	-rm $(DOC) $(DOC:.pdf=.log) $(DOC:.pdf=.aux) \
		$(DOC:.pdf=.out) $(DOC:.pdf=.toc)
