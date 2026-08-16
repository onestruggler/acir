# Literate Agda slides with Beamer — things worth knowing

Notes accompanying `talk.lagda.tex` + `Makefile`. Build with `make`; output lands in
`latex/talk.pdf`.

## Building on this machine (WSL)

Agda, TeX Live and `make` all live in WSL, not on Windows:

```bash
wsl
cd /mnt/c/Users/bones/Documents/work/acir/qpl26slides
make
```

Two things about this directory the Makefile has to know:

- **The module is `qpl26slides.talk`, so the generated `.tex` is one level down.** The
  nearest `.agda-lib` above this directory is the repo's `qupit.agda-lib` (`include: .`),
  which roots the library at the repo root; the module therefore has to be
  `qpl26slides.talk`, and `agda --latex --latex-dir=latex` mirrors the module path and
  writes **`latex/qpl26slides/talk.tex`**, not `latex/talk.tex`. `latexmk` still runs from
  `latex/` — that is where `agda.sty` is, and where the `.pdf` and aux files should land —
  so the rule is `cd latex && latexmk … qpl26slides/talk.tex`. Pointing it at
  `latex/talk.tex` instead is the silent-stale-PDF failure: Agda writes the new file
  where nobody reads it, latexmk recompiles whatever old `latex/talk.tex` is lying around
  (or, once that is deleted, errors), and the PDF never changes.
- **`latex/agda.sty`.** Ubuntu's `agda-bin` package does not ship the default `agda.sty`,
  so Agda's "drop a copy into the output directory" step dies with
  `/usr/share/libghc-agda-dev/latex/agda.sty ... does not exist`. The file that is now in
  `latex/` came from the v2.8.0 tag of the Agda repo (link at the bottom of this file).
  Keep it — `make clean` already leaves it alone — and commit it with the sources, since
  Agda cannot regenerate it here.

## Use LuaLaTeX or XeLaTeX, not pdfLaTeX

pdfLaTeX needs a `\newunicodechar` line for every exotic glyph, which never ends. With
LuaLaTeX/XeLaTeX you load `fontspec` + `unicode-math` and pick a font with wide coverage
(DejaVu works well) and Agda's alphabet soup just renders.

```latex
\usepackage{fontspec}
\usepackage{unicode-math}
\setmainfont{DejaVu Serif}
\setsansfont{DejaVu Sans}
\setmonofont{DejaVu Sans Mono}
\setmathfont{Latin Modern Math}   % or XITS Math / DejaVu Math TeX Gyre
```

LuaLaTeX can additionally chain fallback fonts so missing glyphs get borrowed instead of
coming out as tofu:

```latex
\usepackage{luaotfload}
\directlua{luaotfload.add_fallback
  ("agdafallback",
    { "DejaVuSans:style=Regular;"
    , "NotoSansMath:style=Regular;"
    , "Symbola:style=Regular;"
    }
  )}
\defaultfontfeatures{RawFeature={fallback=agdafallback}}
```

Load `\usepackage{agda}` *after* the font setup.

## No `[fragile]` frames

`agda --latex` turns code blocks into ordinary LaTeX markup before Beamer ever sees them,
so `verbatim`-style catcode trickery isn't involved and `[fragile]` isn't needed.

## Hidden preamble code goes outside any frame

The module header and imports have to be real Agda code, but you don't want them on a
slide:

```latex
\begin{code}[hide]
{-# OPTIONS --without-K --safe #-}

module talk where

open import Agda.Builtin.Nat using (Nat; zero; suc)
\end{code}
```

Note the `using (...)`: `Agda.Builtin.Nat` also exports `_+_`, so an unrestricted import
clashes if you define your own addition.

## Overlays: `\pause` can't go inside a code block

Split the code into several blocks and wrap them in `AgdaMultiCode`, which keeps the
columns aligned across blocks *and* suppresses the extra vertical space between them
(it is `AgdaAlign` + `AgdaSuppressSpace` combined). `\pause` between blocks then works.

```latex
\begin{AgdaMultiCode}
\begin{code}
+-identityʳ : ∀ m → (m + zero) ≡ m
\end{code}
\pause
\begin{code}
+-identityʳ zero    = refl
\end{code}
\pause
\begin{code}
+-identityʳ (suc m) rewrite +-identityʳ m = refl
\end{code}
\end{AgdaMultiCode}
```

The same trick hides a boring middle section while keeping the visible parts aligned —
just use `\begin{code}[hide]` for the middle block instead of `\pause`.

Neither `AgdaAlign` nor `AgdaSuppressSpace` may be nested.

## `[inline]` is still a code block

`\begin{code}[inline]` is inline in the *typeset* output only; the literate parser treats
it like any other block, and both of the obvious one-liners fail:

- **`\end{code}` must start its own line.** Written mid-sentence, as in
  `\begin{code}[inline]Nat → Nat\end{code} is an endofunction`, Agda swallows the rest of
  the document as code and reports a `ParseError` pages later.
- **The content must be a top-level declaration, not an expression.** `Nat → Nat` on its
  own is a parse error; `Endo = Nat → Nat` is fine.

So the working shape is

```latex
The abbreviation \begin{code}[inline]
Endo = Nat → Nat
\end{code}
names the endofunctions on the naturals.
```

Also, no `\verb` in the surrounding prose: a Beamer frame that is not `[fragile]` cannot
carry it, and the failure is a bare `Missing } inserted` at `\end{frame}`. Use
`\texttt{\textbackslash end\{code\}}` instead. (The Agda code blocks themselves are fine —
that is the whole point of the note above.)

## Highlighting a token: hook `\AgdaFormat`

`\AgdaFormat` sees every token as `{name}{rendered}`, so you can intercept one of them.
Two traps, both hit while testing this template:

1. **Define the parameterized macro in the preamble.** Beamer re-scans the body of a
   frame, so a `\newcommand`/`\renewcommand` with `#1` *inside* a frame dies with
   `Illegal parameter number in definition of \iterate`.
2. **Don't wrap the `\renewcommand` and the code block in an extra `{ }` group inside the
   frame.** That combination silently swallows the entire code block — no error, just a
   blank slide. A frame is already a group, so the redefinition is local anyway.

Preamble:

```latex
\newcommand{\Highlighted}{}
\renewcommand{\AgdaFormat}[2]{%
  \ifthenelse{\equal{#1}{\Highlighted}}{\alert{#2}}{#2}}
```

In a frame:

```latex
\begin{frame}{Drawing attention}
  \renewcommand{\Highlighted}{double}%
  \begin{code}
quadruple : Nat → Nat
quadruple n = double (double n)
  \end{code}
\end{frame}
```

## `agda.sty` and `make clean`

`agda --latex --latex-dir=latex` drops a default `agda.sty` into the output directory the
first time. If you customise it (colours, `\AgdaCodeStyle`, …), make sure `make clean`
doesn't delete it — the shipped Makefile deliberately leaves it alone.

`clean` also has to sweep up the beamer leftovers `latexmk -c` doesn't know about
(`.nav`, `.snm`, `.ptb`, …). Spell them out rather than writing `talk.{nav,snm,…}`:
make recipes run under `/bin/sh`, which has no brace expansion, so that form silently
deletes nothing.

Useful package options: `\usepackage[bw]{agda}` (black and white), `[conor]` (Epigram 1
colours), `[links]` (clickable identifiers), `[references]` (`\AgdaRef`).

## Other knobs

| Knob | Effect |
| --- | --- |
| `\setlength{\mathindent}{1em}` | pulls code toward the left margin — slides are narrow |
| `\renewcommand{\AgdaEmptySkip}{0.5\baselineskip}` | tightens blank lines inside code |
| `\begin{code}[inline]` | typesets a snippet inline in a sentence (`inline*` adds a trailing space) |
| `\begin{code}[number=lbl]` | numbered, referenceable code listing |
| `--only-scope-checking` | fast preview build, skips typechecking |
| `--count-clusters` | better alignment with combining characters (needs an Agda built with cluster counting) |

Redefining the `\Agda…FontStyle` commands to an explicit monospace family also kills TeX
ligatures, so `--` inside an Agda identifier doesn't become an en dash:

```latex
\newfontfamily{\AgdaCodeFont}{DejaVu Sans Mono}[Scale=0.75]
\renewcommand{\AgdaFontStyle}[1]{{\AgdaCodeFont #1}}
% … same for \AgdaKeywordFontStyle, \AgdaStringFontStyle,
%   \AgdaCommentFontStyle, \AgdaBoundFontStyle
```

## HTML slides instead?

The alternative route is `.lagda.md` → `agda --html` → Pandoc/reveal.js. You lose Agda's
column alignment, which is usually the reason people reach for the LaTeX backend in the
first place.

## Sources

- [JLimperg/agda-beamer-template](https://github.com/JLimperg/agda-beamer-template)
- [Generating LaTeX — Agda docs](https://agda.readthedocs.io/en/latest/tools/generating-latex.html)
- [Literate Programming — Agda docs](https://agda.readthedocs.io/en/latest/tools/literate-programming.html)
- [`beamer-luaxelatex.lagda.tex`](https://github.com/agda/agda/blob/master/doc/user-manual/tools/beamer-luaxelatex.lagda.tex)
- [`agda.sty`](https://github.com/agda/agda/blob/master/src/data/latex/agda.sty)
