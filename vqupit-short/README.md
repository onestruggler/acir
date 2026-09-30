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
place; later the same day, §3 (*Two Routes to Completeness*) was
condensed into the closing paragraph of §2 — the follows/departs
statement, as in the long version — and the sections renumbered.

## What was kept, and where

The five pages keep every result and every design decision of the long
version, at a density of roughly one sentence per paragraph of the
original:

| §  | Content | Long version |
|----|---------|--------------|
| 1  | The problem, the method (factor, present, compose), what is checked | §1 |
| 2  | Qupit Clifford gates and quotients; three examples of the encoding, each as Agda code beside its circuit picture (the swap as a word, two constructors of the rule family, a five-step derivation); **Theorem 1** (`clifford-presentation`) and **Theorem 2** (`unique-nf`) as Agda types; the route — we mostly follow the paper, with one major divergence at the boosting step, and why | §2, §4 |
| 3  | The symplectic factor: semantics, the doubly inductive normal form (its datatype and box pictures quoted from the long version's §4.2), the coset table with its soundness law in code, uniqueness, completeness by `by-normalization` | §5 |
| 4  | Composing: the Pauli factor, the semidirect product, plumbing (semidirect → Simplified-V1 → Paper-V0 → Paper-V1), the scalars and the one correction $\omega^{(p^2-1)/8}$ | §6 |
| 5  | What is verified and what is not, statistics, the use of Claude, related work (trimmed 2026-09-30 to formal verification in proof assistants), future work | §7, §8, §9 |
| A  | The fifteen simplified rules and the sixteen exact rules as circuit equations, the chain of presentations, the size table (the normal-box figure removed 2026-09-30) | Figure 2, Table 2 |
| B  | *An Introduction to the Framework*, verbatim: the $S_n$ walkthrough — gates and circuits, the two axioms and the structural rules, cosets, the staircase normal form and the coset table `ract` with its soundness law, the tower, semantics, uniqueness, completeness, and the presentation record `_IsPresentationOf_`; plus B.5, the semidirect product (ℤ_N)ⁿ ⋊ S_n (a former warm-up of the long version, condensed, cited from §4) | §2 |

What did **not** survive: the framework summary that used to be §4 (the
five coset-table hypotheses in prose, the semidirect and extension
theorems, the two warm-ups in one sentence — the presentation record,
the coset table and its soundness law are now shown on $S_n$ in
Appendix C instead), the product constructions (the long version's
§3), the worked examples ($S$ meeting a spine, $M_xM_y = M_{xy}$), the
`respects-Δ` listing, the nine-family table of box relations, the
`act≡ap`/`abstract` anecdote, the proof-engineering discussion
including its three headline lessons, the `Home:` module names under
the theorems, the paragraph on the use of a language model (one
sentence remains, now an AI-contribution statement), the figure
drawing the sixteen rules as
circuit equations (for the rules, see the qupit paper's Figure~1),
and the well-definedness argument for the coset table (the coset half
semantic, the residual half by cancellation, the tower a well-founded
induction on the width — the long version's §5), and the
relation-reduction paragraph (the box relations derived from the full
seventeen axioms, the simplified fifteen, `Simplified.Iso`; the
fifteen remain drawn in Figure 1 and listed in part in Appendix B).  The
long version's `notes/survey-*.md` still record the file and line of
every fact.

Appendix A exists because the main text refers to the rule figures,
the boxes and the size table; Appendix B is where the main text sends
the reader for the library.  The former Appendix B, *Selected Agda
Definitions* (the five coset-table hypotheses, the six one-qupit
simplified rules, the conjugation action), was removed 2026-09-30;
its box-label sets moved into the boxes figure's caption.

## Files

- `main.tex` — the driver, the long version's preamble minus the
  `listings` fallback, with the same `\aid{…}`/`\aidop{…}`,
  `\fitfig`/`\ufig`/`\ufigT` macros and PACMPL metadata.  Drop
  `anonymous` for a camera-ready.
- `sections/*.tex` — plain LaTeX, one file per section (`abstract`,
  `intro`, `background`, `symplectic`, `composing`,
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
  Only `thm-clifford`, `thm-unique`, `thm-sp`, `thm-lm`, `thm-exact`,
  `rows` and `nf` are used; the others are kept for
  re-expansion.  The four exceptions are `ex-circuit`, `ex-relation`
  and `ex-reasoning`, the examples of §2 (the swap as a word, two
  constructors of the rule family, and a five-step derivation), and
  `ex-table`, §3's statement of the coset table and its soundness
  law: they
  are this folder's own, rendered by `make agda` from
  `lagda/ex-*.lagda.tex` over the shared scope `lagda/Prelude.agda`,
  which postulates the gates and the congruence so that each snippet
  fits on a few lines; `lagda/Check.agda` typechecks the derivation
  against it with the width pinned (the printed snippet leaves the
  width implicit, as the library does inside a module parameterised
  by it).
  Their figures `def-Ex-eq` (the slides' `def-Ex` with `=` for `≡`)
  and `pv0-conj-Ex-Hup-steps` (the derivation as a chain of circuits
  joined by `≈`) are `Chain` items of `../Cir2Tikz/src/qpl26.hs`.
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
