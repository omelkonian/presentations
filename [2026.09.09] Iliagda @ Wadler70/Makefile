MAIN=main

AGDA=$(HOME)/.cabal/bin/agda-2.8.0 --latex --latex-dir=latex
LATEX=xelatex -halt-on-error -interaction=nonstopmode

PRE=agda.sty preamble.tex
SRCS=$(wildcard src/*.lagda)
DEPS=$(patsubst src/%.lagda, src/latex/%.tex, $(SRCS))
IMGS=$(wildcard img/*)

.PHONY: default check clean
default: $(MAIN).pdf

src/latex/%.tex: src/%.lagda
	cd src && $(AGDA) $*.lagda

$(MAIN).pdf: $(MAIN).tex $(PRE) $(DEPS) $(IMGS)
	$(LATEX) $(MAIN).tex
	$(LATEX) $(MAIN).tex

# full typecheck of every literate module (the default pipeline already
# typechecks; this target just forces a clean re-run)
check:
	cd src && for f in *.lagda; do $(AGDA) $$f || exit 1; done

clean:
	rm -rf *.aux *.log *.out *.nav *.snm *.toc *.ptb *.vrb \
	       $(MAIN).pdf src/latex src/_build
