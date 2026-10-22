# PLanQC 2027 talk proposal: Human-Made Scaffolds for Machine-Written Proofs

An extended abstract for [PLanQC 2027](https://popl27.sigplan.org/home/planqc-2027),
the workshop on Programming Languages for Quantum Computing at POPL 2027,
derived from the OOPSLA draft in `../oopsla`. It keeps the final results
of that paper and leaves its details out: the form of a theorem, the
sixteen formalizations with their sizes and typechecking times, what the
formalization found (the gap in Hadamard-Π, the relation r_K missing from
Amy, Ross and Wesley's Toffoli–Hadamard presentation, the misprints), and
how the proofs were produced.

## The call

- 2–5 page abstracts, single-column 11pt `acmsmall`, not counting
  references; links to longer preprints are welcome.
- Talk proposals: accepted authors give a talk or a poster. No formal
  proceedings; abstracts are posted on the workshop site.
- Submission deadline: Friday 30 October 2026 (AoE). Notification:
  27 November 2026. Workshop: 12 January 2027.
- Submission site: https://planqc27.hotcrp.com

On 22 October 2026 the body ends on page 5 and the references take
pages 5–6.

## Building

    make

runs `latexmk -pdf` on `main.tex` (`acmart` with
`acmsmall,nonacm,11pt,screen`). In this setup TeX lives in WSL:

    wsl --exec bash -lc 'export PATH=/home/bonest/texlive/bin/x86_64-linux:$PATH; cd /mnt/d/work/acir/planqc && make'

`agda-style.sty` and `refs.bib` are copies of those in `../oopsla`; keep
them in step if either changes. They differ in one entry: the POPL paper
on the library is `anonymous2027popl` there, with its authors withheld
for review, and `bian2027popl` here, by Xiaoning Bian and Yuan Feng. Every Unicode character in an Agda
snippet needs an entry in the `literate` table of `agda-style.sty`.

## Before submission

- The authors are Xiaoning Bian, Yuan Feng, Sarah Meng Li and John van
  de Wetering, with the affiliations and e-mail addresses of
  `../vqupit/main.tex`. Yuan Feng's address there is marked as a guess
  (`../vqupit/README.md`); confirm it.
- The numbers (modules, lines, typechecking times, the four weeks) are
  those of the OOPSLA draft, measured on 22 October 2026 on the
  `ten-completeness` branch. Re-measure them if the developments change.
- The abstract says that LLM coding agents wrote fifteen of the sixteen
  developments; check that this and the acknowledgement of AI use match
  the workshop's policy, as for the OOPSLA draft.
