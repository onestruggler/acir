# Makefile — build the Tsinghua PL seminar slides (beamer, 16:9).
#
# Usage (from WSL, inside slides/Tsinghua-PL-seminar/):
#   make          # Agda's LaTeX backend on sections/*.lagda.tex, then lualatex
#   make agda     # only regenerate latex/slides/.../sections/*.tex
#   make png      # render every slide to png/sNN.png for a quick look
#   make clean    # remove latexmk auxiliary files (keeps main.pdf)
#   make cleanall # also remove main.pdf, png/ and the generated latex/
#
# From PowerShell:
#   wsl --exec make -C /mnt/c/Users/bones/Documents/work2-home/acir/slides/Tsinghua-PL-seminar
#
# Code highlighting works as for the paper (../../paper): the sections
# that quote Agda are literate Agda files.  `agda --latex
# --only-scope-checking' resolves every name against the library (so
# identifiers are coloured by kind) and writes
# latex/slides/Tsinghua-PL-seminar/sections/<name>.tex, which main.tex
# \inputs.  Snippets from other branches (the "new since the paper"
# part) are declared in hidden blocks, so that they scope-check here.
# Agda runs from the repository root, where qupit.agda-lib lives.
#
# Engine: lualatex (fontspec; Fira Sans/Fira Math for text, JuliaMono
# for Agda code).

ROOT      := ../..
HERE      := slides/Tsinghua-PL-seminar
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

# Agda copies agda.sty from its data directory into the output
# directory unless one is already there; the Debian package lacks it,
# so put ours there first.
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
	rm -f main.nav main.snm main.vrb

cleanall: clean
	rm -rf main.pdf png latex
