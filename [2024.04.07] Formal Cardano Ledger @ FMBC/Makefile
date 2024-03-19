MAIN=main
AGDA?=agda
RUN_AGDA=$(AGDA) -i. --latex --only-scope-checking
LATEX?=xelatex
RUN_LATEX=$(LATEX) -shell-escape -halt-on-error -interaction=non-stop

.PHONY: default clean
default: $(MAIN).pdf

latex/%.tex : %.lagda
	$(RUN_AGDA) $<

%.pdf: %.tex
	$(RUN_LATEX) $<

DEPS=$(patsubst %.lagda, latex/%.tex, $(shell find . -type f -name '*.lagda'))

$(MAIN).tex: $(DEPS)

clean:
	rm -rf *.aux *.log *.out *.bbl *.lof *.blg *.lot *.gz *.toc *.ptb *.dvi \
	       *~ *.agdai _build/ latex/
	       $(MAIN).pdf
