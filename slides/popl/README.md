# POPL talk — *Normal Forms and Complete Relations for Circuits in Agda*

Main-track talk (about 20 minutes, 23 numbered frames, beamer 16:9),
built from the paper in `../../paper` only.

## Build

From WSL, in this directory:

```
make            # agda --latex on sections/*.lagda.tex, then latexmk -lualatex
make png        # every slide as png/sNN.png
make cleanall   # remove main.pdf, png/ and the generated latex/
```

Agda runs from the repository root (where `qupit.agda-lib` lives), so the
quoted code is scope-checked against the library and every identifier
gets Agda's colour, exactly as in the paper. Needs Agda 2.8 with the
standard library, LuaLaTeX with beamer/metropolis, pgfplots, and the
fonts Fira Sans, Fira Math, STIX Two Math, JuliaMono, DejaVu Sans.

## Structure and timing

| part | frames | minutes |
|---|---|---|
| Completeness proofs are gigantic; this paper | 2 | 2 |
| Running example: swap circuits (gates, axioms, cosets, coset table, tower) | 5 | 6 |
| Design decisions 1–2 and the completeness lemma | 4 | 4 |
| Verified coset tables: engine, towers, evaluation, indices, constructions | 5 | 5 |
| Catalogue: what is verified, families, Matsumoto–Amano | 3 | 2 |
| Setoids vs. quotients, cost and limitations, related work, takeaways | 4 | 2 |

## Files

- `main.tex` — preamble and the order of the parts.
- `sections/*.tex` — `motivation`, `closing` (no Agda).
- `sections/*.lagda.tex` — `example`, `design`, `engine`, `evaluation`,
  `constructions`, `catalogue`: literate Agda, rendered by Agda's LaTeX
  backend into `latex/slides/popl/sections/`. The fragments are the
  paper's; `evaluation` quotes `Examples/Amalgamations/CliffordT1.agda`
  and declares its context in a hidden block.
- `figures/`, `agda.sty`, `circuits.tikzstyles` — copied from `../../paper`.
