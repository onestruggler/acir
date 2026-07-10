# POPL submission draft — "Normal Forms and Complete Relations for Circuits in Agda"

Generated 2026-07-09/10 from `paper-outline.md` and the repository state
(see `PROGRESS.md` for the full phase log, and `notes/` for the verified
fact base the text was written from).

## Files

- `main.tex` — acmart driver (`acmsmall,review,anonymous`; PACMPL/POPL
  metadata; CCS concepts; the `\aid{…}` inline-code macro; acks are inside
  `\begin{acks}` and therefore hidden while the `anonymous` option is on).
- `sections/*.tex` — one file per section, `\input` from `main.tex`:
  `abstract`, `intro`, `permutations` (worked example, 3 quantikz figures),
  `preliminaries`, `design`, `examples` (catalogue + 2 tables), `related`
  (comparison + table), `discussion` (stats + lessons), `conclusion`.
- `refs.bib` — ~50 entries, every one verified against a live source during
  writing; entries marked `%% VERIFY-DETAIL` have one detail (page range,
  volume) taken from standard knowledge — re-check before camera-ready.
- `agda-style.sty` — `listings` language definition for Agda with a full
  Unicode `literate` table (for code blocks) and a mirrored
  `\DeclareUnicodeCharacter` block (for Unicode inside `\aid`/prose under
  pdfLaTeX).
- `notes/` — working notes: `repo-survey.md` (the verified catalogue of
  theorems, with file/line references), `related-work.md` (per-item
  comparison notes with citation keys).
- `TASK-BRIEF.md`, `PROGRESS.md` — automation contract and phase log; not
  part of the submission.

## Building

No TeX toolchain was available on the authoring machine, so the sources are
compile-clean by construction and mechanical audit (balanced environments,
brace balance, cite/label consistency, Unicode coverage) but have **not**
been compiled. To build:

```
latexmk -pdf main.tex          # pdflatex route (Unicode handled by the
                               # literate + DeclareUnicodeCharacter tables)
# or, if a Unicode engine is preferred:
latexmk -lualatex main.tex
```

Required packages: `acmart`, `listings`, `booktabs`, `pifont`, `quantikz`
(v2; pulls in TikZ), plus the local `agda-style.sty`. On TeX Live:
`texlive-publishers` (acmart), `texlive-pictures`/`quantikz`,
`texlive-latex-extra`.

First-compile checklist (expected small fixups):

1. `quantikz` figure spacing in `sections/permutations.tex` may need
   column/row-sep tweaks to taste.
2. If pdflatex complains about a Unicode character, add it to **both**
   tables in `agda-style.sty` (the `literate` list and the
   `\DeclareUnicodeCharacter` block) following the existing entries.
3. Resolve the `%% VERIFY-DETAIL` comments in `refs.bib` (page numbers,
   LIPIcs/LNCS volumes) before camera-ready.
4. Page budget: the draft targets a full-length PACMPL submission; trim
   `design.tex`/`related.tex` first if over.

## Relation to the Agda code

- Every Agda snippet in the paper is quoted verbatim from the repository;
  `notes/repo-survey.md` records the source file and line for each.
- `MainTheorems.agda` (repository root) is the index module the paper
  refers to; it restates all headline theorems with full types and
  typechecks together with the four standard roots:

  ```
  wsl --exec /home/onest/.cabal/bin/agda MainTheorems.agda
  ```

- The paper deliberately claims nothing from `Examples/Groups/Symplectic/`
  or `Examples/Groups/Pauli/Semantics.agda` (work in progress, does not
  typecheck as of writing); if that changes, `sections/examples.tex`
  (\S "Work in progress") and `sections/conclusion.tex` are the places to
  update.

## Anonymity

The `anonymous` option suppresses authors and acks. Prior work by the
repository's authors is cited in the third person throughout, per
double-blind convention. The artifact is cited as anonymous supplementary
material (`qupit-code` in `refs.bib`).
