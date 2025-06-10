MAIN=main

AGDA=agda-2.7.0 -isrc/ --latex --latex-dir=. --only-scope-checking
LATEX=xelatex -shell-escape -halt-on-error -interaction=non-stop

PRE=agda.sty preamble.tex
DEPS=$(patsubst %.lagda, %.tex, $(shell find . -type f -name '*.lagda'))
# DEPS=

.PHONY: default clean $(DEPS)
default: $(MAIN).pdf

# %.tex : %.lagda
# 	$(AGDA) $<

%.pdf: %.tex $(PRE)
	$(LATEX) $<

$(MAIN).pdf : $(DEPS)

clean:
	rm -rf *.aux *.log *.out *.bbl *.lof *.blg *.lot *.gz *.toc *.ptb *.dvi \
	       *.pdf *~ *.agdai _build/ \
	       $(MAIN).tex $(MAIN).pdf $(DEPS)
