# Agda/Lean comparison (Section 3.3)

These scripts measure the two formalizations and write `../figures/compare.tex`,
the figure `fig:compare`. Every number in Section 3.3 and in `tab:compare` is
printed by `figdata.py`. Python 3, no dependencies. Run from this folder:

```sh
python loc.py ../.. loc.json            # code lines per row
python features.py ../.. features.json  # options, postulates, tactics, noncomputable, imports
python3 leantime.py ../../Lean leantime.json   # in WSL: clean timed Lean build, about 1-3 h
python3 agdatime.py ../.. agdatime.json        # in WSL: from-scratch Agda check, per module, about 1 h
python figdata.py                       # combine with the check times; print totals
python mkfig.py ../figures/compare.tex  # the pgfplots figure
```

* **Rows.** `loc.py` maps each row of Table 1 to its Agda folders (the qudit
  Clifford row is `Symplectic`, `ProjectiveClifford/Qupit`, `Clifford+MinusOne`,
  `ProjectivePauli` and `Qupit-Clifford`, Table 1's 215 modules) and to
  `Lean/QCert/<Row>`. The shared library is `Word`, `Presentation`, `Circuit`,
  `Normalization`, `Examples/Construct` and the small groups in Agda, and
  `Presentation`, `Circuit`, `Exact`, `Matrix`, `NumberTheory`, `Synthesis` in Lean.
* **Code lines** exclude blank lines and comments (`--`, nested `{- -}` / `/- -/`).
  They count every file under version control, generated ones (certificates,
  derivations) and, in Agda, those ported from the authors' Clifford+T and
  Clifford+CS proofs included; untracked work in progress is not counted, and
  Lean's generator templates under `gen/` are not modules and are left out.
* **Proof features** (`features.py`) are counted over the written files, those
  whose header does not say they are generated or ported (`loc.kind`);
  `noncomputable` declarations and Lean's `by` blocks and automation calls are
  counted both there and over all files, and Section 3.3 quotes the counts over
  all files.
* **Check times.** The Agda times are measured by `agdatime.py`: it removes
  the repository's Agda interfaces (keeping the standard library's and
  EucDomain's), then checks the shared library and each row in one Agda
  process each, through a root importing every tracked module of the unit,
  with `--profile=modules`; a row's time is the sum of the times Agda reports
  for its own modules, each without its imports, wherever it was checked.
  A module that does not typecheck (a stale one that nothing imports) is left
  out, with what imports it, and recorded (`excluded`). `agdatime.json` keeps
  every module's time, and per unit the wall time, the peak resident size and
  the CPU that other projects' Lean or Agda used meanwhile; logs go to
  `~/agdatime-logs/`. The Lean times are measured by `leantime.py`: it removes QCert's
  build artifacts (keeping Mathlib), then builds each folder of `Lean/QCert`
  and each root module in dependency order of their imports with
  `LEAN_NUM_THREADS=2 lake build <its modules>`, timing each, so that every
  module is counted in its own folder. It holds `check.sh`'s lock and records,
  per folder, the load and whether another project's Lean was running
  (`foreign`); such a folder can be re-timed alone (`leantime.py ../../Lean
  leantime.json Folder,...`). `leantime.json` records the run (date, revision,
  CPU, memory). Logs go to `~/leantime-logs/`.

## Four formalizations of Toffoli–Hadamard (`tab:th4`)

`th4.py` compares the four formalizations of Amy, Ross and Wesley [2024] as
two Agda–Lean pairs: `CCX+H-3qubit-Tietze` (Table 1's row) against
`QCert/ToffoliHadamard` (written from the paper), and `CCX+H-3qubit-RS`
against `QCert/ToffoliHadamardRS`, its translation to Lean (one proof in
both assistants). It counts code lines as `loc.py` does, and code
characters (non-blank characters outside comments), which do not depend on
how a generator lays out its output. It times each folder as `agdatime.py`
and `leantime.py` time a row: an untimed check first, so that everything the
folder imports is built, then the folder's own interfaces or build artifacts
removed and the folder checked again, Agda's time the sum of its per-module
profile and Lean's the wall time of `LEAN_NUM_THREADS=2 lake build`. In WSL,
under the Agda lock (it takes `check.sh`'s Lean lock itself):

```sh
python3 th4.py ../.. th4.json                 # about 15 minutes
TH4_LINES=1 python3 th4.py ../.. th4.json     # recount, keep the times
```

`th4.json` is the measurement of 8 November 2026 (revision `ede28959`) on
the Intel Core i5-14400, with no other proof assistant running; Table 1's
times are from the i5-13400TEF, so its Toffoli–Hadamard row differs (111 and
135 s there, 103 and 125 s here). Logs go to `~/th4-logs/`.

Panel (a) of `fig:compare` takes its Toffoli–Hadamard row from `th4.json`, the
second pair (one proof in both assistants), where Table 1's two proofs take
different routes; panel (b) and the totals of `tab:compare` keep Table 1's
folders. `figdata.py` reads it, so rerun `figdata.py` and `mkfig.py` after `th4.py`.

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

`exec.json` is the measurement of 3 November 2026 (revision `ac567f88` plus
the working tree) on an Intel Core i5-14400 under WSL. `loc.json`,
`features.json` and `leantime.json` were remeasured on 5 November 2026, after
the Lean typechecking speed-up (merge `e19af70c`); `leantime.json` says on
which machine. Its clean run (5 November, kept as `leantime-run1.json`)
overlapped another project's Lean builds, so the twenty units they overlapped
were re-timed on 6 November (`retimes`); `leantime.json` holds each unit's
last timing. `agdatime.json`, `loc.json` and `features.json` were measured on
8 November 2026, on the same machine as `leantime.json`, after the
`MainTheorem` modules were added (revision `88440624`).
