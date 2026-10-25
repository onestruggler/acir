# Makefile — build the POPL submission PDF.
#
# Usage (from WSL, inside the paper/ directory):
#   make          # run Agda on the literate sections, then latexmk
#   make agda     # only regenerate latex/paper/sections/*.tex from the
#                 # sections/*.lagda.tex files (needs the Agda library
#                 # one directory up: the snippets import it)
#   make lua      # build via lualatex (fallback for Unicode in running text)
#   make watch    # continuous rebuild on save (latexmk -pvc)
#   make diff     # latexdiff against the submitted version: diff.tex, diff.pdf
#   make png      # render every page to png/pNN.png (needs gs) for a quick look
#   make clean    # remove latexmk auxiliary files (keeps main.pdf)
#   make cleanall # also remove main.pdf, png/ and the generated latex/
#
# From PowerShell (make, TeX Live and Agda live in WSL):
#   wsl bash -lc "make -C /mnt/d/work/acir/paper"
#
# Code highlighting: the three sections that quote Agda are literate
# Agda files (sections/*.lagda.tex).  `agda --latex --only-scope-checking`
# scope-checks their code blocks against the library (so every name is
# resolved and coloured by kind, without requiring the fragments to
# typecheck) and writes latex/paper/sections/<name>.tex, which main.tex
# \inputs.  agda.sty is Agda's own style file; the copy in this
# directory is the one Agda generates into latex/.
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
AGDA     := agda
AGDAFLAGS := --latex --only-scope-checking --latex-dir=paper/latex

SECTIONS := $(wildcard sections/*.tex)
LAGDA    := $(wildcard sections/*.lagda.tex)
AGDATEX  := $(patsubst sections/%.lagda.tex,latex/paper/sections/%.tex,$(LAGDA))
FIGURES  := $(wildcard figures/*.tikz)
DEPS     := $(MAIN).tex $(SECTIONS) $(FIGURES) refs.bib agda-style.sty agda.sty circuits.tikzstyles

.PHONY: all agda lua watch png diff clean cleanall

all: $(MAIN).pdf

agda: $(AGDATEX)

# Agda must run from the repository root, where the .agda-lib file lives
# and relative to which the literate sections are named
# paper.sections.<name>.
latex/paper/sections/%.tex: sections/%.lagda.tex
	cd .. && $(AGDA) $(AGDAFLAGS) paper/$<

$(MAIN).pdf: $(DEPS) $(AGDATEX)
	$(LATEXMK) -pdf $(LMKFLAGS) $(MAIN).tex

lua: $(AGDATEX)
	$(LATEXMK) -lualatex $(LMKFLAGS) $(MAIN).tex

watch: $(AGDATEX)
	$(LATEXMK) -pdf -pvc $(MAIN).tex

png: $(MAIN).pdf
	mkdir -p png
	gs -q -dNOPAUSE -dBATCH -sDEVICE=png16m -r80 -sOutputFile=png/p%02d.png $(MAIN).pdf

# latexdiff of this revision against the submitted version.  submitted/
# holds the sources of the PDF the reviewers read (paper/ of the
# supplementary material).  Agda code blocks, figures and the acks are
# compared as wholes; latexdiff leaves the old listings (agdacode, a
# verbatim environment) out of the diff; the bibliography is the
# current one (main.bbl is moved aside so that it is not flattened).
# The three figures the revision replaced are taken from submitted/.
LDCONFIG := --config="PICTUREENV=(?:picture|DIFnomarkup|code|tikzpicture|acks)[\w\d*@]*" \
            --config="VERBATIMENV=(?:comment|agdacode)"

diff: diff.pdf

diff.tex: $(DEPS) $(AGDATEX) $(wildcard submitted/*.tex submitted/sections/*.tex)
	[ ! -f $(MAIN).bbl ] || mv $(MAIN).bbl $(MAIN).bbl.keep
	latexdiff --flatten --encoding=utf8 $(LDCONFIG) submitted/$(MAIN).tex $(MAIN).tex > $@; \
	  s=$$?; [ ! -f $(MAIN).bbl.keep ] || mv $(MAIN).bbl.keep $(MAIN).bbl; exit $$s
	sed -i -e 's,{figures/fig\(1_sigma\|2_comm2\|2_yb\)},{submitted/figures/fig\1},g' $@

diff.pdf: diff.tex
	$(LATEXMK) -pdf -interaction=nonstopmode diff.tex

clean:
	$(LATEXMK) -c $(MAIN).tex
	[ ! -f diff.tex ] || $(LATEXMK) -c diff.tex
	rm -f comment.cut $(MAIN).ptb diff.ptb

cleanall: clean
	rm -rf $(MAIN).pdf diff.tex diff.pdf png latex
