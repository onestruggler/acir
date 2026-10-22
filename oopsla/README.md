# OOPSLA draft: Human-Made Scaffolds for Machine-Written Proofs

This folder is a draft OOPSLA paper on the formalization work done in
this repository since the POPL paper on the library (branch
`popl-revision1`, folder `paper/`). It covers the sixteen developments
under `Examples/Groups/` (and `Examples/Independence/`) that came after
it: the two-level groups, the circuit theories, the qudit Clifford
chain of the `qupit` branch (Symplectic, ProjectivePauli,
ProjectiveClifford/Qupit, Qupit-Clifford, Clifford+MinusOne/Qupit),
Blake's minimality theorem, and the gap in Hadamard-Pi with Clément's
repair.

## Building

    make

runs `latexmk -pdf` on `main.tex`. In this setup TeX lives in WSL:

    wsl --exec bash -lc 'cd /mnt/d/work/acir/oopsla && make'

The WSL TeX Live here lacks `binhex.tex`, which `newtxmath` (loaded by
`acmart`) inputs but does not use. A full TeX Live has it. Otherwise
put an empty `binhex.tex` on `TEXINPUTS`.

The Agda snippets use the `agdacode` listings environment of
`agda-style.sty`. Every Unicode character in a snippet needs an entry in
its `literate` table, and every one in running text a
`\DeclareUnicodeCharacter`; a missing one gives "Invalid UTF-8 byte
sequence".

## Before submission

- The author block is anonymous (`acmart` option `anonymous`). The
  entry `anonymous2027popl` in `refs.bib` is our POPL paper. Fill in
  its authors and venue once it is public.
- The qudit Clifford paper (`bian2026qupit`, arXiv:2609.40106) is ours
  and says in its abstract that its completeness is verified in Agda.
  Section 3.3 cites it in the third person, but a reviewer who reads
  that abstract can link the two. Decide whether to keep it, and check
  the venue's rules on citing one's own work.
- The acknowledgements say that the formalization and this draft were
  written with Claude Code. Check that this matches the venue's policy
  on AI disclosure, and adjust the wording to what we did.
- The numbers of the corpus table and the typechecking table (modules,
  lines, times), the totals in the abstract and introduction, and the
  dates and commits of the method section were measured on the
  `ten-completeness` branch on 22 October 2026, the times by per-module
  profiling (`--profile=modules`) of a from-scratch check; the
  generated lines of the appendix table, but for three rows, on the
  `v-office` branch on 13 October. Re-measure them if the
  developments change.
- The errata are cited as supplementary material (Section 5.1). They
  are `errata/errata.tex`, a standalone document listing every error
  found, source by source, with the module that checks each
  correction; build it with `latexmk -pdf errata.tex` in that folder.
  Update it when the findings change.
- The body must end by page 23 (OOPSLA 2027 limit, excluding
  references and appendices). On 22 October 2026 the conclusion ends
  on page 23 and the references start on page 24.
