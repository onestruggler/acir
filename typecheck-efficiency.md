# Typechecking efficiency

What has made modules of this library check faster, what did not, and how
to measure. The target is every module under 20 s of its own checking
time, with 30–40 s acceptable for large modules. Developments with their
own performance notes (Real-Clifford+CH's stored-matrix evaluations, the
abstract readings `⟦_⟧ₒ`, CNOT+Dihedral's tables, …) keep them in
`CLAUDE.md`; this file collects the general techniques.

## Measuring

- **Measure a module's own time, in CPU.** `agda --profile=modules`
  prints the time spent in each module, imports excluded; that and not
  wall time is the number to compare. Timings vary by about ±15 % while
  other Agda processes share the machine, so only trust differences that
  survive a back-to-back comparison of the old and new file.
- **Measure from scratch.** Agda skips a module whose interface is
  current, so time in a fresh export (`git archive HEAD`) or after
  deleting the module's `.agdai`.
- **Batch the modules.** One Agda process per module spends 8–10 s
  reloading the interfaces it imports. Checking about twenty consecutive
  modules (in dependency order) through one generated root that imports
  them halves a whole-library timing run.
- **Find the cost inside a module per definition.** `agda
  --profile=definitions M.agda` (on its own: it cannot be combined with
  `modules`) prints the time of every definition, where-block
  definitions included (`M.Descent._.low`), after deleting `M.agdai`;
  that found both hotspots below at once. Timing successive prefixes —
  cut the file before top-level declarations (before clauses also
  works: coverage fails only at the end) — is the fallback, and is
  coarser. `--profile=internal` gives the phases (typing, coverage,
  positivity, serialisation).
- **Do not probe with holes.** Replacing proofs by `?` makes Agda
  postpone constraints and can make a module *slower* (30 s against
  21 s), so it does not measure what the replaced proofs cost.
- **Cap the heap and watch the host.** Run under `+RTS -M…`; on Windows
  the binding limit is the commit limit, not the RAM, and exhausting it
  restarts the whole WSL VM with every job in it.

## What worked

| Technique | Where | Effect |
|---|---|---|
| Remove a `with` whose test computes anyway | `BR/Two/L2-CZ/Left`, `Pushing/Push2` | 51.7 → 5.8 s, 19.1 → 2.1 s |
| Merge clauses that differ only in an argument nothing splits on | `BR/Two/D`, `L2-CZ/Left` | part of 20.7 → 2.7 s |
| `--lossy-unification` | `BR/Calculations`, `BR/Two/D`, `L2-CZ/Left`, `Simplified-V1/Iso`, `CCX+HH-TwoLevel/QuadXEBase` | 15.3 → 1.1 s, 20.7 → 2.7 s, −40 %, −17 %, 126 → 11.7 s |
| Apply reasoning modules once, not per clause | `Simplified-V1/Forward`, `Simplified-V1/Iso` | 23.0 → 10.8 s, −20 % |
| Share duplicated rewrite rules through `then` | `Ex-Sym3n/Swap` | 21.0 → 15.4 s |
| Split only on what blocks reduction, not on every intermediate result | `Construct/Properties/Amalgamation` | 54.6 → 25.1 s (profile total) |

- **A `with` normalises the goal before abstracting.** `with b ≟ c`
  where `b` is a successor and `c` is zero is `no` by computation, so the
  `with` only costs: Agda first normalises the whole goal, here deep into
  ℤ/pℤ arithmetic under `--call-by-name`. Drop it and take `neq` from an
  absurd where-function (`neq : b ≢ c ; neq ()`); the goal then reduces
  as needed. The same holds for any `with` on a term that reduces at the
  clause's patterns. (`CLAUDE.md`'s Clifford+MinusOne pitfall — never
  `with`-abstract a term whose definition is large at symbolic p — is the
  same mechanism.)
- **Clauses that differ only in a pattern nobody inspects.** A proof
  written once for `b@₀` and once for `b@(₁₊ _)` with identical bodies is
  elaborated twice; one clause with `b` a variable does. That needs the
  functions in its goal to reduce with `b` a variable: their case trees
  must not split on `b` first. Agda builds a case tree from the first
  clause that matches, splitting on its leftmost constructor pattern, so
  reordering the callee's clauses (disjoint clauses, so the function is
  unchanged — it only reduces in more cases) can make the merge possible
  (`D.agda`: `dir-of`'s `S-gen` clauses moved above its `H-gen` ones).
- **Definitional steps by `refl`.** A rewriting tactic used to prove an
  equality that holds by definition (`rewrite-sym0 100 auto` for
  `[ ₀ , d ]ᵇ ≡ Ex • CX'^ d`) can be replaced by `refl`.
- **`--lossy-unification`.** Compatible with `--safe` and not infective:
  importers need no change. It gave the largest single gains where
  solving implicit words and field terms dominated (`Calculations`:
  13×). It can pick a wrong solution where a constraint has several; name
  the implicit argument there (`Iso`: `by-assoc {v = SemiDirect.H ^ 4}`).
  It gave nothing measurable on `Paper-V0/Lemmas`, `Powers` or
  `Forward`, so measure it back to back before adding it. **Try it
  first** where the time sits in conversion checks between terms headed
  by defined functions — levels of matrices, `Low`/`Path` over words,
  `actMʷ w M`. In `QuadXEBase` (profile total 146 s, one where-definition
  82 s) several rounds of restructuring found that a right-hand side cost a
  minute when its expected type spelled the state as `actMʷ T1w σ` and
  nothing behind a type alias, and that inlining `bridge` and giving
  the pieces alias types brought the total to 58 s; the flag alone, on
  the unchanged file, brought it to 22 s, and with it the restructuring
  was unnecessary.
- **Module applications cost, per application.** `open M args` copies
  every definition `M` exports into the current module, and those copies
  then go through positivity, dead-code analysis and serialisation.
  `Forward`'s `f-well-defined` opened `PB`, `PP` and `SR` (Presentation
  Base, Presentation Properties, setoid reasoning) in the where block of
  each of its ~38 clauses; one private module parameterised by the width
  (`module Clifford-Reasoning {n : ℕ} where open … public`), opened once,
  halved the module. Two caveats: a type that itself opens `PB` with the
  same renaming then sees two `_≈_`s (drop its `let`, the shared module
  provides it), and a name whose type does not mention the width
  (`Pattern-Assoc`'s `□`) leaves the width unsolved (open it at the
  width: `open Pattern-Assoc {₁₊ m}`). Where the blocks are few or the
  modules small (`Powers`) the gain is within noise.
- **A `with` chain splits only on what blocks reduction.** A proof about
  functions defined by `with` tends to repeat their whole chain — `with
  f x | inspect f x`, then `with g y | inspect g y` on the pieces, seven
  levels deep, in every combination of cases. But a `with` whose pattern
  is a pair (`… | (w′ , c′)`) is a record pattern, translated to
  projections, so a function defined that way (`_ᵗ`, the traversals
  built on it, `hcmw`) reduces at any argument; only a split on a
  constructor that is not a record (`inj₁`/`inj₂`) blocks. So abstract
  just those scrutinees, let the rest reduce, and finish with the
  lemma that is really needed (`rewrite lemma-hcxds-m …`); `inspect` is
  unnecessary when nothing uses its equation. Where two traversals must
  agree, abstract the proof that they do together with them (`with h u
  | h v | h-wd u v p … | (c₁ , refl)`): the `refl` identifies their
  results and the impossible mixed cases disappear. `lemma-hcd-mb-•`
  went from ~60 deep clauses to 12 two-level ones (15.1 → 0.7 s), two
  claims of `hhh-wd-ax` from 3.3 and 2.7 s to under 0.4, and the
  module's unattributed `Miscellaneous` time (which includes writing the
  interface) from 18.3 to 12.3 s.
- **One step function, not two copies.** `step-swap` restated
  `step-swap0`'s sixteen rules verbatim; it is now
  `step-swap-extra then step-swap0`. With `then` the extra rules are
  tried first, which reorders rules only where their patterns are
  disjoint, so every word rewrites to the same list and the
  `rewrite-swap … auto` proofs of its importers are unchanged.

## Memory

- **Cap every Agda process** (`+RTS -M…`) and record its peak with
  `+RTS -s` ("bytes maximum residency"). A module that overflows a 3 GB
  heap on its own is a target in itself; see `CLAUDE.md` for the known
  ones and for what fixed others (`ItemB`'s module application
  re-exporting all of `Frame`: 3.3 GB → 1 GB).
- **On Windows the limit is the host's commit, not the VM's RAM.** WSL's
  VM counts against Windows' commit limit, and so does the page cache
  Linux keeps; `.wslconfig` may allow the VM more memory than Windows
  can commit, in which case running out crashes the whole VM (every job
  in it) instead of letting Linux kill one process. Several sessions
  each running Agda with an 8 GB heap did that every two minutes here.
  Dropping the VM's clean page cache (`echo 1 >
  /proc/sys/vm/drop_caches`, as root) when Windows' free commit runs low
  returned 1–3 GB at a time and kept it up; the lasting fixes are
  `autoMemoryReclaim=dropcache` under `[experimental]` in `.wslconfig`,
  or a `memory=` below what Windows can commit.
- **Fewer with-functions, smaller interfaces.** Each `with` creates an
  auxiliary function whose type carries the abstracted goal; deep chains
  of them are serialised into the interface and loaded by every
  importer. Compacting `Amalgamation`'s chains (above) cut the time its
  profile attributes to no definition, writing the interface included,
  by a third.

## What did not help

- **Returning the rebuilt list from `Rewriting.Step.multistep`.** The fix
  that made `Presentation/Tactics/Words`' loops linear (see `CLAUDE.md`)
  made no measurable difference to `Presentation/Tactic/Rewriting`'s
  users: the duplication it removes bites only under `--call-by-name`.
- **Splitting a step function into named pieces** so that another module
  can reuse them: each function pays its own coverage and case-tree cost,
  which ate the saving (+2 s on `Powers` for −4 s on `Swap`).
- **Hoisting only the cheap module applications** (`Powers`: 6 %).

## Known costs without a cheap fix

- **Rewrite-step functions over width-indexed generators.** Under
  `--cubical-compatible`, each clause of a step function matching long
  lists of `Gen (₁₊ n)` patterns costs about 0.5 s (`Powers` checks in
  7 s under `--without-K` and 14 s under `--cubical-compatible`; its
  importers need the latter). Removing it would mean step functions over
  a non-indexed representation of the generators.
- **Diffuse cost.** `Paper-V0/Lemmas` (≈21 s) spends its time over
  hundreds of explicit reasoning steps, no definition more than 2.5 s.
  Splitting such a file at its natural module boundaries, with the old
  module kept as a re-export, brings each file under the target without
  reducing the total.
