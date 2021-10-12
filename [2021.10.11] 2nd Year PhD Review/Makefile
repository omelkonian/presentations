MAIN=2nd-year-report
TEX=
AGDA=agda -i. --latex --latex-dir . --only-scope-checking

SRC=*.tex $(MAIN).bib

default: all
all: $(MAIN).pdf


%.tex : %.lagda
	$(AGDA) $<

$(MAIN).pdf: $(MAIN).tex 0-diagrams.tex
	xelatex -shell-escape -pdf -f -halt-on-error -cd $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi *.snm *.nav $(MAIN).pdf

.PHONY: default all clean
