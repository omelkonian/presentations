MAIN=msc-defence
STYLE=stylish.fmt

default: all
all: $(MAIN).pdf

redo:
	xelatex $(MAIN).tex

$(MAIN).pdf: $(MAIN).tex
	xelatex $(MAIN).tex

%.tex : %.lagda $(STYLE) 1-intro.lagda 2-utxo.lagda 3-bitml.lagda 4-future.lagda
	lhs2TeX --poly -o $@ $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi *.snm *.nav $(MAIN).tex $(MAIN).pdf

.PHONY: default all clean redo
