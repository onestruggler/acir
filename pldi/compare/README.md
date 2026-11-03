# Agda/Lean comparison (Section 3.3)

These scripts measure the two formalizations and write `../figures/compare.tex`,
the figure `fig:compare`. Every number in Section 3.3 and in `tab:compare` is
printed by `figdata.py`. Python 3, no dependencies. Run from this folder:

```sh
python loc.py ../.. loc.json            # code lines per row
python features.py ../.. features.json  # options, postulates, tactics, noncomputable, imports
python figdata.py                       # combine with Table 1's check times; print totals
python mkfig.py ../figures/compare.tex  # the pgfplots figure
```

* **Rows.** `loc.py` maps each row of Table 1 to its Agda folders (the qudit
  Clifford row is `Symplectic`, `ProjectiveClifford/Qupit`, `Clifford+MinusOne`,
  `ProjectivePauli` and `Qupit-Clifford`, Table 1's 215 modules) and to
  `Lean/QCert/<Row>`. The shared library is `Word`, `Presentation`, `Circuit`,
  `Normalization`, `Examples/Construct` and the small groups in Agda, and
  `Presentation`, `Circuit`, `Exact`, `Matrix`, `NumberTheory`, `Synthesis` in Lean.
* **Code lines** exclude blank lines and comments (`--`, nested `{- -}` / `/- -/`).
  They count every file, generated ones (certificates, derivations) and, in
  Agda, those ported from the authors' Clifford+T and Clifford+CS proofs
  included; Lean's generator templates under `gen/` are not modules and are
  left out.
* **Check times** are those of Table 1, copied into `figdata.py`.

## Execution benchmark (panel (c))

Both programs decide, for random circuits `w` of 100 gates over H, S and CZ
on n wires, that `w` and `w S⁴` have the same matrix, each with the
procedure its Clifford soundness proof uses (Agda: `⟦_⟧ᴳ` and `check` of
`Qubit-Clifford/Semantics/Interpretation`, products of stored Gaussian
matrices; Lean: `Sim.check`, simulation on every basis vector over ℤ[ω]).
They draw the same circuits from the same generator and time themselves
with the monotonic clock. In WSL:

```sh
# Agda (GHC backend; under the Agda lock; the module is not --safe: it binds GHC's clock)
cd /mnt/d/work2/acir
agda --compile --compile-dir=$HOME/agda-bench --ghc-flag=-O2 pldi/compare/bench/CliffordBench.agda
# Lean (native executable `cliffordbench`, target in Lean/lakefile.lean)
cd Lean && lake build cliffordbench
# run both, write exec.json, redraw
cd ../pldi/compare && python3 runbench.py exec.json && python3 mkfig.py ../figures/compare.tex
```

`exec.json` records each configuration's three trials and their median, and
the date and CPU.

The JSON files are the measurements of 3 November 2026 (revision `ac567f88`
plus the working tree) on an Intel Core i5-14400 under WSL.
