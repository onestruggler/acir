#!/usr/bin/env bash
# Regenerate every .tikz from the Haskell sources in src/, then build test3.pdf.
#   usage:  ./build.sh            # generate tikz + build test3.pdf
#           ./build.sh gen        # generate tikz only
#
# Run this from the Cir2Tikz directory.  Generators write into figures/, which
# is where \tikzfig looks after failing to find NAME.tikz beside the .tex, so
# the \tikzfig{...} calls name pictures without any directory prefix.
# Compiler and LaTeX droppings go to build/; the .pdf is copied back beside its
# .tex source.
set -e

# GHC may be a Homebrew keg-only install (off the default PATH); on systems
# without brew, just use whatever ghc is already there.
if command -v brew >/dev/null 2>&1 && brew --prefix ghc@9.12 >/dev/null 2>&1; then
  export PATH="$(brew --prefix ghc@9.12)/bin:$PATH"
fi

mkdir -p build figures/chains figures/v1

echo ">> compiling src/main.hs"
ghc --make -O0 -isrc src/main.hs -o build/main_local -odir build -hidir build

echo ">> running generators (figures/, figures/chains/, figures/v1/)"
./build/main_local
runghc -isrc src/figs.hs
runghc -isrc src/v1rels.hs

if [ "${1:-}" != "gen" ]; then
  for doc in test3 v1rels; do
    echo ">> pdflatex $doc.tex (x2)"
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build \
             "$doc.tex" >/dev/null
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build \
             "$doc.tex" >/dev/null
    cp "build/$doc.pdf" .
    echo ">> wrote $doc.pdf"
  done
fi
