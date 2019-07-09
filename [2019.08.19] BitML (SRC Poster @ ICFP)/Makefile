MAIN=bitml-poster
STYLE=stylish.fmt

default: all
all: $(MAIN).pdf

redo:
	xelatex $(MAIN).tex

$(MAIN).pdf: $(MAIN).tex
	xelatex $(MAIN).tex

%.tex : %.lagda $(STYLE) beamerthemeI6pd2.sty
	lhs2TeX --poly -o $@ $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi *.snm *.nav $(MAIN).tex $(MAIN).pdf

.PHONY: default all clean redo
