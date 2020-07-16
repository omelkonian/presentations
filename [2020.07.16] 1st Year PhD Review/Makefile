MAIN=1st-year-report

SRC=*.tex $(MAIN).bib

default: all
all: $(MAIN).pdf

$(MAIN).pdf: $(SRC)
	# rm -f $(MAIN).bbl
	xelatex $(MAIN)
	# bibtex $(MAIN)
	# xelatex $(MAIN)
	# xelatex $(MAIN)

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi *.snm *.nav $(MAIN).pdf

.PHONY: default all clean
