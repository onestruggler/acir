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

**Status: builds clean.**  `latexmk -pdf main.tex` produces `main.pdf`
(26 pages) with zero errors, zero undefined citations/references, zero
missing characters, and zero overfull boxes (verified 2026-07-10 with
TeX Live in WSL, pdflatex route).

```
latexmk -pdf main.tex          # verified (Unicode handled by the
                               # literate + DeclareUnicodeCharacter tables)
```

Debian/Ubuntu packages used for the verified build:
`texlive-latex-recommended texlive-latex-extra texlive-fonts-recommended
texlive-fonts-extra texlive-publishers texlive-pictures texlive-science
texlive-plain-generic latexmk` (the last of these supplies `binhex.tex`,
which acmart needs), plus the local `agda-style.sty`.

Remaining pre-submission checklist:

1. Resolve the `%% VERIFY-DETAIL` comments in `refs.bib` (page numbers,
   LIPIcs/LNCS volumes) before camera-ready. BibTeX also warns about
   empty `address`/`publisher` on EPTCS entries — cosmetic.
2. If a new Unicode character is added to the text, add it to **both**
   tables in `agda-style.sty` (the `literate` list and the
   `\DeclareUnicodeCharacter` block) following the existing entries.
3. Page budget: 26 pages in `acmsmall` review mode; check the target
   POPL cycle's limit and trim `design.tex`/`related.tex` first if over.

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
