MAIN=main
PRE=agda.sty $(MAIN).agda-lib
AGDA=agda -i. --latex --latex-dir=. --only-scope-checking
LATEX=xelatex -shell-escape -halt-on-error # -interaction=batchmode # -pdf -f -cd

.PHONY: default all clean
default: all
all: $(MAIN).pdf

%.tex : %.lagda
	$(AGDA) $<

%.pdf: %.tex $(PRE)
	$(LATEX) -output-directory=$(dir $@) $<
	bibtex $* &> /dev/null

main.tex: \
  $(patsubst %.lagda, %.tex, $(shell find . -type f -name '*.lagda'))

redo :
	$(LATEX) $(MAIN).tex
	bibtex $(MAIN) &> /dev/null

clean:
	rm -rf *.aux *.log *.out *.bbl *.lof *.blg *.lot *.gz *.toc *.ptb *.dvi \
	       $(MAIN).pdf *~ *.agdai _build/
