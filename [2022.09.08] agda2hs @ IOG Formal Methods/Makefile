MAIN=main
AGDA=agda-erased
TEX=xelatex -shell-escape -pdf -f -halt-on-error -cd

default: all
all: $(MAIN).pdf

%.tex : %.lagda
	$(AGDA) -i. --latex --latex-dir . $<

$(MAIN).pdf: $(MAIN).tex
	$(TEX) $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi \
	      *.snm *.nav *.vrb *.run.xml *blx.bib $(MAIN).tex $(MAIN).pdf

.PHONY: default all clean
