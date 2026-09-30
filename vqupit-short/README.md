# "Verified Generators and Relations for Qupit Clifford Operators" — five-page version

A compression of `../vqupit` (the 26-page OOPSLA/PACMPL draft; 23 pages
of text) to **five pages of text** in the same format
(`acmart`, `acmsmall,review,anonymous`), followed by the references and
an appendix.  Generated 2026-09-27 from the sources of `../vqupit`
at their state on branch `qupit`; nothing here was written from other
material, and every count, name and line count is the long version's.
Revised 2026-09-30: the one-page summary of the framework (the former
§4) was removed from the main text, and the long version's §2, *An
Introduction to the Framework*, was copied into the appendix in its
place.

## What was kept, and where

The five pages keep every result and every design decision of the long
version, at a density of roughly one sentence per paragraph of the
original:

| §  | Content | Long version |
|----|---------|--------------|
| 1  | The problem, the method (factor, present, compose), what is checked | §1 |
| 2  | Qupit Clifford gates and quotients; three examples of the encoding, each as Agda code beside its circuit picture (the swap as a word, two constructors of the rule family, a five-step derivation); **Theorem 1** (`clifford-presentation`) and **Theorem 2** (`unique-nf`) as Agda types | §2 |
| 3  | The paper's route, why it was not formalised, our route | §4 |
| 4  | The symplectic factor: semantics, the doubly inductive normal form, the coset table and its well-definedness by semantics, uniqueness, the relation reductions (66 → 42 families → 17 → 15) | §5 |
| 5  | Composing: the Pauli factor, the semidirect product, plumbing (semidirect → Simplified-V1 → Paper-V0 → Paper-V1), the scalars and the one correction $\omega^{(p^2-1)/8}$ | §6 |
| 6  | What is verified and what is not, statistics, lessons, related work (all citations kept), future work | §7, §8, §9 |
| A  | The sixteen rules as circuit equations, the normal boxes, the chain of presentations, the size table | Figures 1, 2, Table 2, box table |
| B  | Four Agda listings the text refers to: the normal-form datatype, the five coset-table hypotheses, the six one-qupit simplified rules, the conjugation action | code blocks of §3–§6 |
| C  | *An Introduction to the Framework*, verbatim: the $S_n$ walkthrough — gates and circuits, the two axioms and the structural rules, cosets, the staircase normal form and the coset table `ract` with its soundness law, the tower, semantics, uniqueness, completeness, and the presentation record `_IsPresentationOf_` | §2 |

What did **not** survive: the framework summary that used to be §4 (the
five coset-table hypotheses in prose, the semidirect and extension
theorems, the two warm-ups in one sentence — the presentation record,
the coset table and its soundness law are now shown on $S_n$ in
Appendix C instead), the product constructions (the long version's
§3), the worked examples ($S$ meeting a spine, $M_xM_y = M_{xy}$), the
`respects-Δ` listing, the nine-family table of box relations, the
`act≡ap`/`abstract` anecdote, the proof-engineering discussion beyond
its three headline lessons, the `Home:` module names under the
theorems, and the paragraph on the use of a language model (one
sentence remains).  The
long version's `notes/survey-*.md` still record the file and line of
every fact.

Appendices A and B exist because the main text refers to the rule
figure, the boxes and the size table, and because the four listings are
the most information-dense way to show what the Agda actually says;
Appendix C is where the main text sends the reader for the library
(three references: the introduction, the presentation record under
Theorem 1, and the coset-table hypotheses of Appendix B).

## Files

- `main.tex` — the driver, the long version's preamble minus the
  `listings` fallback, with the same `\aid{…}`/`\aidop{…}`,
  `\fitfig`/`\ufig`/`\ufigT` macros and PACMPL metadata.  Drop
  `anonymous` for a camera-ready.
- `sections/*.tex` — plain LaTeX, one file per section (`abstract`,
  `intro`, `background`, `routes`, `symplectic`, `composing`,
  `discussion`, `appendix`).  Unlike the long version they are **not**
  literate Agda files.  The exception is `sections/permutations.tex`,
  Appendix C: it is `../vqupit/latex/vqupit/sections/permutations.tex`,
  the LaTeX Agda generated from the long version's
  `sections/permutations.lagda.tex`, copied whole (prose and code) with
  two local edits recorded in its header comment; if the long version's
  §2 changes, regenerate there and copy it again.
- `agda/*.tex` — the Agda code blocks, as the LaTeX that Agda's backend
  (`agda --latex --only-scope-checking`) generated for the long
  version's literate sections, copied verbatim from
  `../vqupit/latex/vqupit/sections/*.tex` (so this folder builds with
  `latexmk` alone; no Agda is needed).  If a snippet changes in the long
  version, regenerate there (`make agda` in `../vqupit`) and copy the
  block again; each file's first line records which block of which section it is.
  Only `thm-clifford`, `thm-unique`, `rows`, `nf`, `hypotheses`,
  `simplified-rules` and `conj` are used; the others are kept for
  re-expansion.  The three exceptions are `ex-circuit`, `ex-relation`
  and `ex-reasoning`, the examples of §2 (the swap as a word, two
  constructors of the rule family, and a five-step derivation): they
  are this folder's own, rendered by `make agda` from
  `lagda/ex-*.lagda.tex` over the shared scope `lagda/Prelude.agda`,
  which postulates the gates and the congruence so that each snippet
  fits on a few lines; `lagda/Check.agda` typechecks the derivation
  against it with the width pinned (the printed snippet leaves the
  width implicit, as the library does inside a module parameterised
  by it).
  Their figures `def-Ex` and `pv0-conj-Ex-Hup` come from
  `../Cir2Tikz/src/qpl26.hs` like the others.
- `figures/*.tikz` — the 64 circuit pictures used (copied from
  `../vqupit/figures/`, do not edit here); `circuits.tikzstyles`,
  `agda.sty`, `agda-style.sty`, `refs.bib` — copied unchanged.
- `Makefile` — `make` (latexmk), `make png`, `make qa`, `make clean`.
- `notes/qa.pl` — checks labels, citations, figure files, listing files
  and Unicode coverage of `\aid{}` and prose (`make qa`).

## Building

```
make            # latexmk -pdf main.tex; no Agda needed
```

Verified 2026-09-30 with TeX Live 2023 (Ubuntu 24.04 packages): `main.pdf`
is 12 pages — **just under 5 pages of text**, the references starting
on the lower half of page 5 and running to page 7, then Appendix A
(pages 7–8), Appendix B (page 8) and Appendix C (pages 9–12) — with
zero errors, zero undefined references or citations and no overfull
box.
(The 2026-09-27 version, with the framework summary as §4 and without
the three examples of §2, was 9 pages: 5 of text, references 6–8,
appendix 8–9.)  The same toolchain rebuilds `../vqupit/main.tex` to
its 26 pages, so page counts are comparable.

## Things to decide

1. The venue.  The page count is measured in `acmsmall`; in the
   two-column `sigplan` format the same text would run about
   three-and-a-half pages, leaving room to restore roughly a third of
   what was cut (start with the worked examples and the listings).
2. Whether to keep Appendix B (the listings) or fold the datatype back
   into §4 at the cost of a quarter page of text.
3. The abstract is 185 words; a venue with a 150-word limit needs two
   sentences fewer.
