MAIN=music-grammars-presentation
STYLE=stylish.fmt

default: all
all: $(MAIN).pdf

redo:
	xelatex $(MAIN).tex

$(MAIN).pdf: $(MAIN).tex
	xelatex $(MAIN).tex

%.tex : %.lhs $(STYLE) 1-intro.lhs 2-ptgg.lhs 3-harmony.lhs 4-melody.lhs 5-rhythm.lhs 6-songs.lhs 7-conclusion.lhs
	lhs2TeX --poly -o $@ $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi *.snm *.nav $(MAIN).tex $(MAIN).pdf

.PHONY: default all clean redo
