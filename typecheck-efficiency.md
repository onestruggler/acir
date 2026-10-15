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
- **Find the cost inside a module by prefixes.** Cut the file before
  successive top-level declarations (before clauses also works: coverage
  fails only at the end) and time each prefix; the increments locate the
  expensive definitions. `--profile=internal` gives the phases (typing,
  coverage, positivity, serialisation); `--profile=definitions` gives
  nothing per definition in Agda 2.8.
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
| `--lossy-unification` | `BR/Calculations`, `BR/Two/D`, `L2-CZ/Left`, `Simplified-V1/Iso` | 15.3 → 1.1 s, 20.7 → 2.7 s, −40 %, −17 % |
| Apply reasoning modules once, not per clause | `Simplified-V1/Forward`, `Simplified-V1/Iso` | 23.0 → 10.8 s, −20 % |
| Share duplicated rewrite rules through `then` | `Ex-Sym3n/Swap` | 21.0 → 15.4 s |

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
  `Forward`, so measure it back to back before adding it.
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
- **One step function, not two copies.** `step-swap` restated
  `step-swap0`'s sixteen rules verbatim; it is now
  `step-swap-extra then step-swap0`. With `then` the extra rules are
  tried first, which reorders rules only where their patterns are
  disjoint, so every word rewrites to the same list and the
  `rewrite-swap … auto` proofs of its importers are unchanged.

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
