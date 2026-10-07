# Tsinghua PL seminar — slides (90 min, beamer 16:9)

*Normal Forms and Complete Relations for Circuits in Agda* — the POPL
submission at tag `popl-revision1` (`../../paper`), plus the developments
on other branches since then.

Every frame title carries a badge: green **in the paper** (the
submission) or orange **new since the paper** (branches `main`,
`popl`, `qupit`, `v-office`, `v-office-Cli-CH`).

## Build

From WSL, in this directory:

```
make            # agda --latex on sections/*.lagda.tex, then latexmk -lualatex
make png        # every slide as png/sNN.png
make cleanall   # remove main.pdf, png/ and the generated latex/
```

From PowerShell:
`wsl --exec make -C /mnt/c/Users/bones/Documents/work2-home/acir/slides/Tsinghua-PL-seminar`

Needs Agda 2.8 with the standard library (the library one directory up
is resolved through `qupit.agda-lib`; Agda runs from the repository
root), TeX Live with LuaLaTeX, beamer/metropolis, quantikz, pgfplots, and
the fonts Fira Sans, Fira Math, STIX Two Math, JuliaMono, DejaVu Sans.

## Layout

- `main.tex` — preamble (theme, fonts, badges, TikZ helpers) and the
  order of the parts.
- `sections/*.tex` — parts without Agda code: `opening`, `motivation`,
  `grouptheory`, `closing`.
- `sections/*.lagda.tex` — parts with Agda code, as literate Agda.
  Agda's LaTeX backend (`--only-scope-checking`) colours every
  identifier by kind and writes `latex/slides/Tsinghua-PL-seminar/sections/*.tex`,
  which `main.tex` inputs. Paper parts (`permutations`, `design`,
  `design2`, `catalogue`) import the library on this branch; the new
  parts (`newcore`, `newqupit`, `newmatrix`, `newrcch`, `newothers`)
  quote code from other branches and declare its context in hidden
  blocks, so they scope-check here too. One block (`lemma-XS`, in
  `design2`) is typeset by hand in Agda's colours and says so.
- `figures/` — circuit figures from the paper (Cir2Tikz/TikZiT);
  `figures/qupit/` — the rule figures of the QPL'26 deck on branch `qupit`.
- `agda.sty`, `circuits.tikzstyles` — copied from `../../paper`.

## Timing (90 min)

| part | frames | minutes |
|---|---|---|
| Why completeness proofs need a machine | 6 | 7 |
| Worked example: permutation circuits | 13 | 15 |
| Normal forms from subgroup chains | 3 | 4 |
| The library, layer by layer | 16 | 18 |
| A catalogue of verified presentations | 9 | 10 |
| New since the paper | 21 | 31 |
| Related work, lessons, outlook | 4 | 5 |
