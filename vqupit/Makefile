# Makefile — build the submission PDF.
#
# Usage (from a WSL shell, inside the vqupit/ directory):
#   make          # build main.pdf via latexmk (pdflatex + bibtex), reruns
#                 # only what changed in main.tex / sections/ / figures/
#   make lua      # build via lualatex (fallback for Unicode in running text)
#   make watch    # continuous rebuild on save (latexmk -pvc)
#   make png      # render every page to png/pNN.png (needs gs) for a quick look
#   make clean    # remove latexmk auxiliary files (keeps main.pdf)
#   make cleanall # also remove main.pdf and png/
#
# From PowerShell (make and TeX live in WSL, on the login-shell PATH):
#   wsl bash -lc "make -C /mnt/d/work/acir/vqupit"
#
# TeX Live on this machine is a user-local install in WSL
# (/home/bonest/texlive); it is added to PATH below if present, so no
# shell setup is needed.  On a machine with a system TeX Live the line
# is harmless.

TEXLIVE_BIN := $(wildcard $(HOME)/texlive/bin/x86_64-linux)
ifneq ($(TEXLIVE_BIN),)
  export PATH := $(TEXLIVE_BIN):$(PATH)
endif

MAIN     := main
LATEXMK  := latexmk
LMKFLAGS := -halt-on-error -interaction=nonstopmode
SECTIONS := $(wildcard sections/*.tex)
FIGURES  := $(wildcard figures/*.tikz)
DEPS     := $(MAIN).tex $(SECTIONS) $(FIGURES) refs.bib agda-style.sty circuits.tikzstyles

.PHONY: all lua watch png clean cleanall

all: $(MAIN).pdf

$(MAIN).pdf: $(DEPS)
	$(LATEXMK) -pdf $(LMKFLAGS) $(MAIN).tex

lua:
	$(LATEXMK) -lualatex $(LMKFLAGS) $(MAIN).tex

watch:
	$(LATEXMK) -pdf -pvc $(MAIN).tex

png: $(MAIN).pdf
	mkdir -p png
	gs -q -dNOPAUSE -dBATCH -sDEVICE=png16m -r80 -sOutputFile=png/p%02d.png $(MAIN).pdf

clean:
	$(LATEXMK) -c $(MAIN).tex
	rm -f comment.cut

cleanall: clean
	rm -rf $(MAIN).pdf png
