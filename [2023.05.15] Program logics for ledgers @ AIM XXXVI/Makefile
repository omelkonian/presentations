MAIN=main
PRE=agda.sty $(MAIN).agda-lib preamble.tex
AGDA=agda -i. --latex --latex-dir=. --only-scope-checking
LATEX=xelatex -shell-escape -halt-on-error # -interaction=batchmode # -pdf -f -cd

.PHONY: default all clean
default: all
all: $(MAIN).pdf

%.tex : %.lagda
	$(AGDA) $<

%.pdf: %.tex $(PRE)
	$(LATEX) $<
	bibtex $* &> /dev/null

$(MAIN).tex : simple.tex simple-example.tex \
              partial.tex partial-example.tex \
	      utxo.tex utxo-example.tex \
	      autxo.tex autxo-example.tex \
	      sound-abstraction.tex

clean:
	rm -rf *.aux *.log *.out *.bbl *.lof *.blg *.lot *.gz *.toc *.ptb *.dvi \
	       *.pdf *~ *.agdai _build/ \
	       $(MAIN).tex \
	       simple.tex simple-example.tex \
               partial.tex partial-example.tex \
	       utxo.tex utxo-example.tex \
	       autxo.tex autxo-example.tex \
	       sound-abstraction.tex
