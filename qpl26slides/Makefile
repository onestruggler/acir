AGDA     = agda
SOURCE   = talk
# The module is qpl26slides.talk (the repo's qupit.agda-lib roots the
# library at the parent directory), so Agda mirrors the module path and
# writes $(LATEXDIR)/$(MODDIR)/$(SOURCE).tex, not $(LATEXDIR)/$(SOURCE).tex.
MODDIR   = qpl26slides
LATEXDIR = latex
LATEX    = latexmk -lualatex -recorder -interaction=nonstopmode -halt-on-error

.PHONY: all watch clean mrproper
all: $(LATEXDIR)/$(SOURCE).pdf

# Force the LaTeX run every time: latexmk decides for itself what to redo.
# latexmk runs in $(LATEXDIR), so agda.sty is found and the pdf and aux
# files land there rather than beside the generated .tex.
.PHONY: $(LATEXDIR)/$(SOURCE).pdf
$(LATEXDIR)/$(SOURCE).pdf: $(LATEXDIR)/$(MODDIR)/$(SOURCE).tex
	cd $(LATEXDIR) && $(LATEX) $(MODDIR)/$(SOURCE).tex

# Agda typechecks the file and emits highlighted LaTeX into $(LATEXDIR).
# It also drops a default agda.sty there the first time.
# Add --only-scope-checking for a fast (unchecked) preview build.
$(LATEXDIR)/$(MODDIR)/$(SOURCE).tex: $(SOURCE).lagda.tex
	$(AGDA) --latex --latex-dir=$(LATEXDIR) $(SOURCE).lagda.tex

watch:
	cd $(LATEXDIR) && latexmk -lualatex -pvc $(MODDIR)/$(SOURCE).tex

# Note: clean does not remove agda.sty, in case you have customised it.
# Recipes run under /bin/sh, which has no brace expansion, so the beamer
# leftovers latexmk -c does not know about are listed one by one.
clean:
	rm -f $(SOURCE).agdai texput.log
	rm -f $(addprefix $(LATEXDIR)/$(SOURCE)., nav snm bbl ptb sh stderr stdout)
	cd $(LATEXDIR) && ([ ! -f $(MODDIR)/$(SOURCE).tex ] || latexmk -c $(MODDIR)/$(SOURCE).tex)
	rm -rf $(LATEXDIR)/$(MODDIR)

mrproper: clean
	rm -f $(LATEXDIR)/$(SOURCE).pdf
