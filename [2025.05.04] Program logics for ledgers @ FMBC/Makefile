MAIN=main
PRE=agda.sty $(MAIN).agda-lib preamble.tex
AGDA=agda -i. --latex --latex-dir=. --only-scope-checking
LATEX=xelatex -shell-escape -halt-on-error -interaction=non-stop

.PHONY: default clean
default: $(MAIN).pdf

%.tex : %.lagda
	$(AGDA) $<

%.pdf: %.tex $(PRE)
	$(LATEX) $<
	bibtex $* &> /dev/null

DEPS=$(patsubst %.lagda, %.tex, $(shell find . -type f -name '*.lagda'))

$(MAIN).pdf : $(DEPS)

clean:
	rm -rf *.aux *.log *.out *.bbl *.lof *.blg *.lot *.gz *.toc *.ptb *.dvi \
	       *.pdf *~ *.agdai _build/ \
	       $(MAIN).tex $(MAIN).pdf $(DEPS)
