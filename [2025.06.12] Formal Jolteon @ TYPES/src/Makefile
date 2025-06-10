# Constants
MAIN=formal-streamlet
AGDA?=agda
AGDA_RUN=$(AGDA) --transliterate
OUT_DIR?=../dist
TEX_ENGINE?=pdflatex
LATEX?=latexmk -$(TEX_ENGINE) -halt-on-error
LATEX_DIR=latex
PRE=$(addprefix $(LATEX_DIR)/,\
  agda.sty references.bib\
  main.tex abstract.tex introduction.tex\
  consensus.tex streamlet.tex consistency.tex testing.tex\
  related.tex outro.tex appendix.tex)

# Agda -> LaTeX -> PDF
latexFiles=$(patsubst %.lagda, $(LATEX_DIR)/%.tex,\
             $(shell find . -name '*.lagda' | sed 's|\.\/||g'))
$(latexFiles): $(LATEX_DIR)/%.tex: %.lagda
	@echo "Compiling $<"
	$(AGDA_RUN) --latex --latex-dir=$(LATEX_DIR) $< # --only-scope-checking

$(OUT_DIR)/$(MAIN).pdf: $(LATEX_DIR)/main.tex $(latexFiles) $(PRE)
	@echo "Generating $@"
	$(eval PDF=$(notdir $@))
	mkdir -p $(dir $@)
	cd $(LATEX_DIR) && $(LATEX) -jobname=$(PDF:.pdf=) $(subst $(LATEX_DIR)/,, $<)
	mv $(LATEX_DIR)/$(PDF) $@

# User commands
.PHONY: default docs clean
default: docs

docs: $(OUT_DIR)/$(MAIN).pdf

clean:
	rm -rf $(LATEX_DIR)/$(MAIN).* $(LATEX_DIR)/*.aux $(LATEX_DIR)/*.fls\
	       $(LATEX_DIR)/*.fdb_latexmk $(LATEX_DIR)/*.log $(LATEX_DIR)/*.out\
	       $(LATEX_DIR)/*.ptb $(LATEX_DIR)/*.vtc\
	       $(LATEX_DIR)/*.bbl $(LATEX_DIR)/*.blg\
	       $(OUT_DIR)/
