# Makefile — build the POPL submission PDF.
#
# Usage (from WSL, inside the paper/ directory):
#   make          # build main.pdf via latexmk (pdflatex + bibtex)
#   make lua      # build via lualatex (fallback for Unicode in running text)
#   make watch    # continuous rebuild on save (latexmk -pvc)
#   make clean    # remove latexmk auxiliary files (keeps main.pdf)
#   make cleanall # also remove main.pdf
#
# Requires TeX Live with latexmk (see README.md for the package list).

MAIN    := main
LATEXMK := latexmk
SECTIONS := $(wildcard sections/*.tex)
DEPS    := $(MAIN).tex $(SECTIONS) refs.bib agda-style.sty

.PHONY: all lua watch clean cleanall

all: $(MAIN).pdf

$(MAIN).pdf: $(DEPS)
	$(LATEXMK) -pdf -halt-on-error -interaction=nonstopmode $(MAIN).tex

lua:
	$(LATEXMK) -lualatex -halt-on-error -interaction=nonstopmode $(MAIN).tex

watch:
	$(LATEXMK) -pdf -pvc $(MAIN).tex

clean:
	$(LATEXMK) -c $(MAIN).tex

cleanall:
	$(LATEXMK) -C $(MAIN).tex
