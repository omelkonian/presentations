MAIN=3rd-year-report

default: all
all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex 0-diagrams.tex
	xelatex -shell-escape -pdf -f -halt-on-error -cd $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi *.snm *.nav $(MAIN).pdf

.PHONY: default all clean
