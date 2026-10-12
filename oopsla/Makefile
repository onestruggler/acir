## Build the paper with latexmk (pdflatex).  In this repository's setup
## TeX lives in WSL:  wsl --exec bash -lc 'cd oopsla && make'
all: main.pdf

main.pdf: main.tex refs.bib agda-style.sty sections/*.tex
	latexmk -pdf -interaction=nonstopmode main.tex

clean:
	latexmk -C main.tex

.PHONY: all clean
