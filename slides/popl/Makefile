# Makefile — POPL talk slides (beamer, 16:9).
#
# Usage (from WSL, inside slides/popl/):
#   make          # Agda's LaTeX backend on sections/*.lagda.tex, then lualatex
#   make agda     # only regenerate latex/slides/popl/sections/*.tex
#   make png      # render every slide to png/sNN.png
#   make clean    # remove auxiliary files (keeps main.pdf)
#   make cleanall # also remove main.pdf, png/ and the generated latex/
#
# As for the paper (../../paper): the sections that quote Agda are
# literate Agda; `agda --latex --only-scope-checking' resolves every
# name against the library, so identifiers are coloured by kind.  Agda
# runs from the repository root, where qupit.agda-lib lives.

ROOT      := ../..
HERE      := slides/popl
AGDA      := agda
AGDAFLAGS := --latex --only-scope-checking --latex-dir=$(HERE)/latex
LATEXMK   := latexmk
LMKFLAGS  := -lualatex -halt-on-error -interaction=nonstopmode

LAGDA   := $(wildcard sections/*.lagda.tex)
AGDATEX := $(patsubst sections/%.lagda.tex,latex/$(HERE)/sections/%.tex,$(LAGDA))
DEPS    := main.tex $(wildcard sections/*.tex) $(wildcard figures/*.tikz) \
           agda.sty circuits.tikzstyles

.PHONY: all agda png clean cleanall

all: main.pdf

agda: $(AGDATEX)

# Agda copies agda.sty from its data directory unless one is already in
# the output directory; some installations lack it, so put ours there.
latex/agda.sty: agda.sty
	mkdir -p latex && cp agda.sty latex/agda.sty

latex/$(HERE)/sections/%.tex: sections/%.lagda.tex latex/agda.sty
	cd $(ROOT) && $(AGDA) $(AGDAFLAGS) $(HERE)/$<

main.pdf: $(DEPS) $(AGDATEX)
	$(LATEXMK) $(LMKFLAGS) main.tex

png: main.pdf
	mkdir -p png
	pdftoppm -r 50 -png main.pdf png/s

clean:
	$(LATEXMK) -c main.tex
	rm -f main.nav main.snm main.vrb main.ptb

cleanall: clean
	rm -rf main.pdf png latex
