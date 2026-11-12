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
  `ProjectivePauli` and `Qupit-Clifford`, Table 1's 216 modules) and to
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

## One proof in both assistants (the Toffoli–Hadamard row of `fig:compare`(a), and the text)

Four Agda–Lean pairs, all in `th4.json`; the text reports three of them.

Table 1's two Toffoli–Hadamard proofs take different routes, so panel (a)
shows, in their place (`*`), `CCX+H-3qubit-RS`, a second Agda proof,
against `QCert/ToffoliHadamardRS`, its translation to Lean.  The text also
compares the 46 modules of `CCX+H-3qubit-Tietze` (Table 1's Agda proof) that
`QCert/ToffoliHadamardTietze` translates with the same Agda modules (the
translation stops before `TwoLevel`; its README says what it covers).  And
it compares `Alt16-RevCir`, the proof of the four-bit theorem that Section 6
and Appendix E follow, with `QCert/Alt16RevCir`, its translation to Lean,
whose `Lib/` translates what the Agda imports from the shared library
(Lafont's presentation of the alternating groups, Symmetric, the PROP layer,
the morphisms of presentations); `th4.py` counts `Lib/` separately
(`lib_code`, `lib_chars`).  The fourth pair, no longer in the text, is
`XCXCCX-4bit`, an earlier proof of the same theorem, with `QCert/XCXCCX4bit`
(forms `Agda XC4`, `Lean XC4`).

For the `Alt16` pair the text also splits Lean's time.  The per-module times
that Lake prints in `~/th4-logs/LeanA16.log` sum to 354 s (the build runs
some modules at the same time; its wall time is the 287.56 s of `th4.json`),
and a module with the folder's imports and no content takes 4.0 to 4.5 s
(`LEAN_NUM_THREADS=2 lean` on a file holding only
`import QCert.Alt16RevCir.Letters`, or only `import QCert.Alt16RevCir.Syntactics`):
loading Mathlib, about 220 s for the 54 modules.

`th4.py` measures these pairs and Table 1's (code lines as `loc.py`
counts them, code characters, the non-blank characters outside comments,
which do not depend on how a generator lays out its output, and check
times as `agdatime.py` and `leantime.py` time a row: an untimed check
first, so that everything the folder imports is built, then the folder's
own interfaces or build artifacts removed and the folder checked again,
Agda's time the sum of its per-module profile and Lean's the wall time of
`LEAN_NUM_THREADS=2 lake build`); `figdata.py` reads it.  `part.py` counts
the translated modules, module by module, the same way, for the text.  In
WSL, under the Agda lock (`th4.py` takes `check.sh`'s Lean lock itself):

```sh
python3 th4.py ../.. th4.json                 # about 25 minutes
TH4_LINES=1 python3 th4.py ../.. th4.json     # recount, keep the times
TH4_FORMS='Agda A16,Lean A16' python3 th4.py ../.. th4.json   # retime some forms
python3 part.py ../.. part.json               # seconds
```

Agda is run with `--library-file=~/acir-agdatime.libraries`, as
`agdatime.py` runs it (`TH4_LIBS`).  `th4.json` is the measurement of
10 November 2026 (revision `4d91b890`) on the Intel Core i5-13400TEF, the
machine of Table 1's times, with no other proof assistant running; the
`Alt16` pair was added to it later that day (revision `f505371e`, recorded
under `retimed` in its `run`), on the same machine, while an idle interactive
Agda session was open and used no CPU.  There
Table 1's Toffoli–Hadamard row took 111.17 and 134.91 s (Agda, Lean, timed
within the whole build) and 110.95 and 118.48 s timed folder by folder here.
`th4-run1.json` keeps the first measurement of the two Toffoli–Hadamard pairs,
on 8 November 2026 (revision `ede28959`) on an Intel Core i5-14400 (103 and
125 s, 44 and 161 s).  Logs go to `~/th4-logs/`.  `part.json` is the count
of 8 November 2026 at revision `1d8511eb`.  Panel (b) and the totals of
`tab:compare` keep Table 1's folders; rerun `figdata.py` and `mkfig.py` after
`th4.py` (`figdata.py` prints the four pairs).  `loc.py`'s `WRITTEN_PATHS`
names two written modules of the `Alt16` pair whose headers its `generated`
heuristic would misread.

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
`MainTheorem` modules were added (revision `88440624`). Their Lean
`RealCliffordCH` entries were recounted on 12 November 2026, after the
two modules of that folder that did not build were deleted (`99d329be`);
nothing else changed in the recount. `leantime.json` keeps the timing of
the build that included them.

`delta.py` gives the numbers of Section 3.6, "Relation to the Earlier
Library": from the repository root, `python delta.py origin/popl-submitted
HEAD` compares the shared library (the `(shared)` entry of `loc.py`) at the
branch of the earlier library and now, module by module, and counts code
lines without blank lines and comments. Run on 12 November 2026: 59 modules
and 8,588 lines then, 92 and 13,172 now; 43 earlier modules remain (15 with
the same code), 16 were removed or reorganized, and 49 are new (6,474 lines).
