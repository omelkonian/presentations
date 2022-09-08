MAIN=agda2hs-iog
AGDA=agda-erased
TEX=xelatex -shell-escape -pdf -f -halt-on-error -cd

default: all
all: $(MAIN).pdf

%.tex : %.lagda
	$(AGDA) -i. --latex --latex-dir . $<

$(MAIN).pdf: $(MAIN).tex
	$(TEX) $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi *.snm *.nav $(MAIN).pdf

.PHONY: default all clean
