# "Verified Generators and Relations for Qupit Clifford Operators" — five-page version

A compression of `../vqupit` (the 26-page OOPSLA/PACMPL draft; 23 pages
of text) to **five pages of text** in the same format
(`acmart`, `acmsmall,review,anonymous`), followed by the references and
a short appendix.  Generated 2026-09-27 from the sources of `../vqupit`
at their state on branch `qupit`; nothing here was written from other
material, and every count, name and line count is the long version's.

## What was kept, and where

The five pages keep every result and every design decision of the long
version, at a density of roughly one sentence per paragraph of the
original:

| §  | Content | Long version |
|----|---------|--------------|
| 1  | The problem, the method (factor, present, compose), what is checked | §1 |
| 2  | Qupit Clifford gates and quotients, circuits in Agda, the sixteen rules, **Theorem 1** (`clifford-presentation`) and **Theorem 2** (`unique-nf`) as Agda types | §2 |
| 3  | The paper's route, why it was not formalised, our route | §3 |
| 4  | The framework: presented monoids, normal forms and `by-normalization`, coset tables and their five hypotheses, the semidirect and extension theorems, the two warm-ups in one sentence | §4, §5 |
| 5  | The symplectic factor: semantics, the doubly inductive normal form, the coset table and its well-definedness by semantics, uniqueness, the relation reductions (66 → 42 families → 17 → 15) | §6 |
| 6  | Composing: the Pauli factor, the semidirect product, plumbing (semidirect → Simplified-V1 → Paper-V0 → Paper-V1), the scalars and the one correction $\omega^{(p^2-1)/8}$ | §7 |
| 7  | What is verified and what is not, statistics, lessons, related work (all citations kept), future work | §8, §9, §10 |
| A  | The sixteen rules as circuit equations, the normal boxes, the chain of presentations, the size table | Figures 1, 2, Table 2, box table |
| B  | Four Agda listings the text refers to: the normal-form datatype, the five coset-table hypotheses, the six one-qupit simplified rules, the conjugation action | code blocks of §4–§7 |

What did **not** survive: the worked examples (the $S_n$ coset table
clause by clause, $S$ meeting a spine, $M_xM_y = M_{xy}$), the
`respects-Δ` listing, the nine-family table of box relations, the
`act≡ap`/`abstract` anecdote, the proof-engineering discussion beyond
its three headline lessons, the `Paper-V1` module map, and the
paragraph on the use of a language model (one sentence remains).  The
long version's `notes/survey-*.md` still record the file and line of
every fact.

The appendix exists because the main text refers to the rule figure,
the boxes and the size table, and because the four listings are the
most information-dense way to show what the Agda actually says; it can
be dropped without breaking any cross-reference except those five.

## Files

- `main.tex` — the driver, the long version's preamble minus the
  `listings` fallback, with the same `\aid{…}`, `\fitfig`/`\ufig`
  macros and PACMPL metadata.  Drop `anonymous` for a camera-ready.
- `sections/*.tex` — plain LaTeX, one file per section (`abstract`,
  `intro`, `background`, `routes`, `framework`, `symplectic`,
  `composing`, `discussion`, `appendix`).  Unlike the long version they
  are **not** literate Agda files.
- `agda/*.tex` — the Agda code blocks, as the LaTeX that Agda's backend
  (`agda --latex --only-scope-checking`) generated for the long
  version's literate sections, copied verbatim from
  `../vqupit/latex/vqupit/sections/*.tex` (so this folder builds with
  `latexmk` alone; no Agda is needed).  If a snippet changes in the long
  version, regenerate there (`make agda` in `../vqupit`) and copy the
  block again; the mapping is recorded in each file's first line.
  Only `thm-clifford`, `thm-unique`, `rows`, `nf`, `hypotheses`,
  `simplified-rules` and `conj` are used; the others are kept for
  re-expansion.
- `figures/*.tikz` — the 38 circuit pictures used (copied from
  `../vqupit/figures/`, do not edit here); `circuits.tikzstyles`,
  `agda.sty`, `agda-style.sty`, `refs.bib` — copied unchanged.
- `Makefile` — `make` (latexmk), `make png`, `make qa`, `make clean`.
- `notes/qa.pl` — checks labels, citations, figure files, listing files
  and Unicode coverage of `\aid{}` and prose (`make qa`).

## Building

```
make            # latexmk -pdf main.tex; no Agda needed
```

Verified 2026-09-27 with TeX Live 2023 (Ubuntu 24.04 packages, acmart
2.10): `main.pdf` is 10 pages — **5 pages of text**, the references
starting on page 5, then 3 pages of references and 2 of appendix — with
zero errors, zero undefined references or citations and no overfull
box.  The same toolchain rebuilds `../vqupit/main.tex` to its 26 pages,
so page counts are comparable.

## Things to decide

1. The venue.  The page count is measured in `acmsmall`; in the
   two-column `sigplan` format the same text would run about
   three-and-a-half pages, leaving room to restore roughly a third of
   what was cut (start with the worked examples and the listings).
2. Whether to keep Appendix B (the listings) or fold the datatype back
   into §5 at the cost of a quarter page of text.
3. The abstract is 170 words; a venue with a 150-word limit needs one
   sentence fewer.
