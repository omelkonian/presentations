MAIN=main
PRE=agda.sty $(MAIN).agda-lib
AGDA=agda -i. --latex --latex-dir=. --only-scope-checking
LATEX=xelatex -shell-escape -halt-on-error -interaction=non-stop

.PHONY: default clean
default: $(MAIN).pdf

%.tex : %.lagda
	$(AGDA) $<

%.pdf: %.tex $(PRE)
	$(LATEX) -output-directory=$(dir $@) $<
	bibtex $* &> /dev/null

NOM_DEPS=$(patsubst %.lagda, %.tex, $(shell find Nominal/. -type f -name '*.lagda'))
ULC_DEPS=$(patsubst %.lagda, %.tex, $(shell find ULC/. -type f -name '*.lagda'))

$(MAIN).pdf: $(NOM_DEPS) $(ULC_DEP)

clean:
	rm -rf *.aux *.log *.out *.bbl *.lof *.blg *.lot *.gz *.toc *.ptb *.dvi \
	       *~ *.agdai _build/ \
	       $(MAIN).pdf $(NOM_DEPS) $(ULC_DEPS)
