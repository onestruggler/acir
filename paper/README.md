# POPL paper — "Normal Forms and Complete Relations for Circuits in Agda"

Sources of the POPL 2027 submission (#911) and of its revision after
the reviews.  `response-911.md` is the author response; `PROGRESS.md`
and `notes/` are the working notes the first draft was written from.

## Files

- `main.tex` — acmart driver (`acmsmall,review,anonymous`; PACMPL/POPL
  metadata; CCS concepts; the `\aid{…}` inline-code macro; acks are inside
  `\begin{acks}` and therefore hidden while the `anonymous` option is on).
- `sections/*.tex` — plain LaTeX sections, `\input` from `main.tex`:
  `abstract`, `intro`, `preliminaries`, `related`, `discussion`,
  `conclusion`.
- `sections/*.lagda.tex` — the three sections that quote Agda code
  (`permutations`, `design`, `examples`) are **literate Agda** files.
  Their `\begin{code}` blocks are typeset by Agda's LaTeX backend, so
  every identifier is coloured by what it is (function, datatype,
  constructor, bound variable, module, …) with Agda's own `agda.sty`.
  Hidden blocks (`\begin{code}[hide]`) import the library and postulate
  whatever context a quoted fragment needs; the visible blocks are the
  fragments as they appear in the paper.  Agda is run with
  `--only-scope-checking`, which resolves and colours every name without
  requiring the fragments to typecheck in isolation.  The rendered
  versions land in `latex/paper/sections/*.tex`, and `main.tex` inputs
  those.
- `agda.sty` — Agda's style file, copied from the `latex/` directory
  Agda generates (regenerate the copy when the Agda version changes).
- `agda-style.sty` — the `\DeclareUnicodeCharacter` table that lets
  pdflatex typeset the Unicode in identifiers (in prose via `\aid`, and in
  the code blocks), plus a `listings` language for Agda that is no longer
  used by the sections but kept as a fallback (`agdacode` environment).
- `figures/*.tikz`, `circuits.tikzstyles` — circuit diagrams generated
  by the Cir2Tikz tool; the `c*` (staircase representatives) and
  `ract-*` figures were taken from the vqupit paper on the `qupit`
  branch.
- `refs.bib` — every entry verified against a live source during writing;
  entries marked `%% VERIFY-DETAIL` have one detail (page range, volume)
  taken from standard knowledge — re-check before camera-ready.
- `notes/` — working notes: `repo-survey.md` (the verified catalogue of
  theorems, with file/line references), `related-work.md` (per-item
  comparison notes with citation keys).
- `TASK-BRIEF.md`, `PROGRESS.md` — automation contract and phase log of
  the first draft; not part of the submission.

## Building

From a WSL shell in this directory:

```
make            # agda --latex on sections/*.lagda.tex, then latexmk -pdf
make agda       # only regenerate latex/paper/sections/*.tex
make png        # render every page to png/ for a quick look
```

From PowerShell: `wsl bash -lc "make -C /mnt/d/work/acir/paper"`.

Requirements: TeX Live with `latexmk` (pdflatex route; the Makefile puts
the user-local `~/texlive` on the PATH if present), and Agda 2.8 with the
library one directory up on its path — the literate sections are the
modules `paper.sections.<name>` of that library, which is why the
Makefile runs Agda from the repository root.  Without Agda, the paper
still builds from a checkout that includes the generated
`latex/paper/sections/*.tex` files, so keep those (and `agda.sty`) in
any source bundle sent to a publisher.

Status: `make` produces `main.pdf` (31 pages in `acmsmall` review mode)
with zero errors, zero undefined citations/references, zero missing
characters and zero overfull boxes (verified 2026-09-09 with the WSL TeX
Live and Agda 2.8.0).

Checklist before camera-ready:

1. Resolve the `%% VERIFY-DETAIL` comments in `refs.bib`.
2. If a new Unicode character is used in code or in `\aid`, add it to the
   `\DeclareUnicodeCharacter` block in `agda-style.sty` (pdflatex stops
   with "Unicode character … not set up" otherwise).
3. Page budget: 31 pages in review mode; check the target limit and trim
   `related.tex` or the size table in `discussion.tex` first if over.
4. Anonymity: the `anonymous` option suppresses authors and acks; prior
   work by the authors is cited in the third person; the two web tools
   in §7.5 are cited under the author's name — drop or anonymise those
   citations if the paper goes through another anonymous round.

## Relation to the Agda code

- Every visible Agda block is quoted from the repository and
  scope-checked against it; `notes/repo-survey.md` records the source
  file and line for each.
- `MainTheorems.agda` (repository root) is the index module the paper
  refers to; it restates all headline theorems with full types:

  ```
  wsl --exec /home/bonest/.local/bin/agda MainTheorems.agda
  ```

- An `agda --html` rendering of the whole development (every identifier
  hyperlinked to its definition), promised to the reviewers, is generated
  into `html/` at the repository root by
  `agda --html --html-dir=html MainTheorems.agda`.
