MAIN=eutxoma-presentation

default: all
all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex\
  0-diagrams.tex\
  1-intro.tex\
  2-eutxo.tex\
  3-eutxoma.tex\
  4-metatheory.tex\
  5-related.tex
	xelatex $(MAIN).tex

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi *.snm *.nav $(MAIN).pdf

.PHONY: default all clean
