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
  deleting the module's `.agdai`. Not in a copy another Agda process is
  using: it may rebuild the interface between the deletion and the
  check, and the module then shows no time at all.
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
| `--lossy-unification` | `BR/Calculations`, `BR/Two/D`, `L2-CZ/Left`, `Simplified-V1/Iso`, `CCX+HH-TwoLevel/QuadXEBase`, `Normalization/Pushing/SrelWDM`, `Clifford+CS-TwoLevel/ColumnAction`, `Clifford+CS/Bridge`, `Clifford+T-2qubit-TwoLevel/FourOdd` | 15.3 → 1.1 s, 20.7 → 2.7 s, −40 %, −17 %, 126 → 11.7 s, 31.7 s (over 3 GB) → under 1 s (0.7 GB), 27.2 → 0.4 s, 22.8 → 2.7 s, 24.9 → 7.5 s |
| Apply reasoning modules once, not per clause | `Simplified-V1/Forward`, `Simplified-V1/Iso` | 23.0 → 10.8 s, −20 % |
| Share duplicated rewrite rules through `then` | `Ex-Sym3n/Swap` | 21.0 → 15.4 s |
| Split only on what blocks reduction, not on every intermediate result | `Construct/Properties/Amalgamation` | 54.6 → 25.1 s (profile total) |
| Decide a matrix identity as one boolean, not `refl` on tries | `Clifford/Qubit/Model/Gates` | 71 → 2.9 s |
| Pass the axiom's own words; compare readings as words | `Clifford/Qubit/Model/Faithful` | 1436 → 1.5 s |
| Bundle many module parameters into one record | `Qupit-Phase-Affine/Phase/Control` | 26.9 → 5.3 s |
| Sparse stored products: rows as combinations of rows, no ring operation on 0 or 1 | `Independence/Semantics/Operators`, `Scaled` (all fragments): `Qutrit-Clifford/Semantics`, `Clifford+CS/Semantics`, `Clifford+T/Semantics`, `Clifford+CS/Projective`, `Clifford+CS/Encodings`, `Qutrit-Clifford/Encoding` | 139 → 18.4 s, 63.8 → 22.9 s, 35.2 → 15.8 s, 23.4 → 14.1 s, 46.7 → 33.4 s, 20.9 → 4.0 s |
| Decide a matrix identity as one boolean, not `refl` on the matrices | `Independence/Clifford+CS/Encodings` (32 gate tables over 𝔻[ω]) | 33.4 → 14.4 s (and its client `Clifford+CS/Completeness` 31.6 → 1.8 s after this and the sparse products) |
| A lemma restated at the goal's width, over a word given by an equation | `Independence/Clifford/Bridge`, `Real-Clifford/Bridge` | 51.3 → 6.4 s, 45.5 → 5.4 s |
| Decide an action's instances by one boolean on closed data, not `Eq.refl` per instance | `ProjectiveClifford/Qubit/Selinger/Soundness` | 344 → 3.3 s (+ 1.7 s in the new `LongRelations`) |
| A pair equation's component proved once over variable words, not `Eq.cong proj₁ e` at particular words | `Independence/Qutrit-Clifford/V0Mat` | 149.6 → 8.2 s (1.57 → 1.06 GB) |
| Letters of generated derivations as definitions at a fixed width, not patterns | `Real-Clifford/Relations/Derived`, `Qubit-Clifford/Relations/Rules/Figure5`, `Figure7` | 44.6 → 14.7 s (0.8 GB), 22.5 → 7.9 s, 22.8 → 9.2 s |

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
  was unnecessary. It can also make a module fail: in `U33Di` it solves
  an implicit word of an embedded axiom (`left (left (right (left
  Cyclic.order)))`) by matching the wrong summand, and naming the
  call's endpoints does not help; that module stays without it.
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
- **Decide a stored-matrix identity as one boolean.** `Eq.refl : A ≡ B`
  on two tries makes the conversion checker compare them entry by
  entry, re-evaluating the stored product for every entry. `eqM A B ≡
  true` by `Eq.refl` is one evaluation, and `eqM-sound A B` turns it
  into the equation (`Clifford/Qubit/Model/Decide`, after
  Real-Clifford+CH's `Semantics/Decide`; give both matrices, `eqM` being
  a function). Model.Gates' fifteen relations: 71 → 2.9 s.
- **Compare readings as words, never as operators.** An operator is a
  function, so two readings `⟦ w ⟧`, `⟦ w′ ⟧` that are not syntactically
  identical are compared by applying them and normalising — a sum over
  every intermediate index, exponential in the word. `Model/Faithful`
  proved each axiom by `by-matrix u v eq : ⟦ u ↓ᵏ n ⟧ ≐ ⟦ v ↓ᵏ n ⟧`
  against the expected `⟦ w ⟧ ≐ ⟦ v ⟧`, Figure 8's spelling of the
  same words at width `₃₊ n`: 24 minutes. Now each clause binds the
  axiom's own words (`axiom-sound {w = w} {v} (srel c12)`) and hands
  them to a lemma whose result is `⟦ w ⟧ ≐ ⟦ w′ ⟧` on the nose, with
  the respelling `u ↓ᵏ n ≡ w` checked as words by `Eq.refl`; one lemma
  per arity, so that the width is the axiom's `₃₊ n` rather than `3 +
  n` — a hidden width spelled differently also defeats the syntactic
  check. 1436 → 1.5 s. (The other cure, `CLAUDE.md`'s for
  Real-Clifford+CH, is to make the reading `abstract`.)
- **A long module telescope costs everywhere inside the module.** Every
  metavariable is applied to the whole context, module parameters
  included, so a module with thirty parameters makes every implicit
  argument, every unification and every occurs check thirty arguments
  wider. `Phase/Control`'s `Functor` took the images of the phase
  generators and of nineteen rules as 25 parameters on top of eight
  others; its profile showed the time spread over every definition, with
  the occurs check the largest phase (5.6 s). The same `ctrl-gen` and
  `ctrl-sem`, copied into a module with only the nine parameters they
  use, took 0.9 s against about 10 s in place. Bundling the 25 into a
  record (`Images`, with a constructor, so that the one client wraps its
  arguments in `images (…)`), opened inside the module, took the module
  from 26.9 to 5.3 s; projections of the constructor reduce, so nothing
  downstream changed. Ten per-clause `open Width (₂₊ n)` applications,
  by contrast, cost 0.2 s in all: a module application is cheap when the
  module is small and the context short.
- **In a generated derivation, elaborating the letters is the cost, not
  checking the steps.** `Relations/Derived`'s `derive l r steps refl`
  lists the whole word at every `perm` step, 69 000 letters in all, each
  a pattern synonym (`h₁ = gate₁ H-gate ↥`) whose constructors carry an
  implicit width, so two or three metavariables per letter. For its
  largest equation (341 steps, 11 000 letters) the step list took 3.3 s
  to elaborate and the evaluation by `refl` 0.5 s; a cheaper `perm`
  check (matching letter by letter before sorting into canonical form)
  gained only 20 %. The same cells as ℕ literals took 0.75 s, and as
  definitions opened at a fixed width (`module _ {n : ℕ} where open
  Letters₃ n`, each letter `Gen (₃₊ n)` with nothing left to solve) 1.1 s
  against 4.2 s. `Letters` cannot live beside the patterns: a definition
  in a submodule may not reuse a name its parent defines, so it is its own
  module and `Derived` hides the patterns from `Axioms`. The equations'
  types are unchanged, so nothing downstream changed. (The rewrap is a
  script: indent each run of equations of one width under the block that
  opens its letters.)
- **`Eq.refl` between two computed values is not one evaluation.** The
  conversion checker reduces each side to weak head normal form, then
  compares the components one by one, and each component is reduced
  afresh from the term the previous step left behind; shared work is
  lost in between. `Selinger/Soundness` proved C10, C11 (and C1, C14,
  C15) by `Eq.refl` between the Clifford action of the two sides on
  each concrete Pauli, 16 or 64 cases: a word of 24 letters took 40 ms,
  one of 48 took 3.6 s, and the module 344 s. The same comparison as one
  boolean — `T (agree k u v)`, all 4ᵏ Paulis at width k compared by an
  equality test returning `Bool`, discharged by `tt` — is one reduction:
  96 letters in under 30 ms. To reach width k from the relation's
  arbitrary width, `LongRelations` proves once that a word on the
  bottom k wires, widened, acts on the first k entries as at width k and
  leaves the rest (`local`, letter by letter, every case `refl`).
  Three traps, each of which exhausted a 3 GB heap or left a constraint:
  a lemma stated at width `k ℕ.+ n` gives `cact` a hidden width that is
  not syntactically the goal's `₁₊ n`, and comparing the two evaluates
  the action on a symbolic Pauli — one wrapper per arity, stated at
  `₁₊ n`/`₂₊ n`/`₃₊ n`, fixes it, the width being converted inside the
  wrapper where the word is a variable; `T` is not injective, so `T-∧₁
  _ _ t` cannot find its conjuncts (give them); and `every k _ t P` in a
  where-clause cannot solve `_ P`, `P` being in the metavariable's
  context (give the predicate). `--call-by-name`, which the module
  needed for its assembly, made the old proofs 2.4 times slower still;
  the new ones live in their own module without it.
- **Count the ring operations an evaluation makes.** Independence's
  qutrit semantics checks each axiom as one boolean already, yet
  `Qutrit-Clifford/Semantics` took 134 s, 101 of them on the
  three-wire (I): five products of 27 × 27 matrices over ℤ[ζ₁₂], whose
  every addition and multiplication is a few integer operations on four
  coefficients. Timing pieces separately (one gate built and compared,
  then one, two and four products) put a product at 28 s: summed entry
  by entry over the inner index it makes 27³ zero tests and as many
  additions, nearly all of zeros, for matrices with one non-zero entry
  per row. `mulM` now builds each row of M N as a combination of the
  rows of N with M's row as coefficients, a sum kept as `Maybe` so
  that a zero coefficient costs one zero test and nothing else, and a
  coefficient 1 no multiplication (`term`, `combV`, mirroring `Σv` so
  that `ix-mul` is a short induction): 134 → 24 s. Skipping
  multiplications by 0 and 1 in the Kronecker product of a gate with
  an identity (`tenM`, `_*′_`) and in the final comparison, with the
  two scale factors passed as arguments so that they are computed once
  rather than per entry (`eqWith`), took it to 20 s. Everything goes
  through `ix-mul`/`ix-tenM`/`eqₖ-sound`, whose statements did not
  change, so no client changed.
- **Find the clause, then the spelling.** `Independence/Clifford/Bridge`'s
  `gen` took 40 s; splitting its clauses into named definitions put 41.7
  s on the swap and 0.4 s on the CNOT, two clauses of the same shape —
  `localise {2} {n} u` composed with `bridge u` and the gate's table. The
  difference is the word: the swap's encoding has nine letters, the
  CNOT's three. `localise`'s statement reads the word as `u ↓ᵏ n` at
  width `2 + n`, the goal as `ℰ (gate₂ swap)`, which is `u` itself at
  width `₂₊ n`; equal, but not the same term, so the conversion checker
  compared the two readings by evaluating them. `localise₂` states the
  same at `₂₊ n` over a word `w′` with `w ↓ᵏ n ≡ w′`, checked by `Eq.refl`
  on words: 51.3 → 6.4 s, and the same edit in `Real-Clifford/Bridge`
  45.5 → 5.4 s. The width lemma's own body compares the two spellings
  with the word a variable, which is cheap.
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
- **`--lossy-unification` can lower the peak too.** `SrelWDM` went from
  overflowing a 3 GB heap (1.5 GB peak residency at 8 GB) to 0.7 GB,
  and the `Derived` modules of `Clifford+MinusOne/Qupit/Figure1` and
  `Figure1-MS`, which overflowed it, now fit (1.59 → 1.44 GB peak, 7.3 →
  6.2 s). It did nothing for `Clifford/Qupit/SemRealises`. A module's
  own peak can be far below what a batch reaches: `Selinger/Translation`
  overflowed 3 GB in a batch that also rechecked other modules, and
  peaks under 1 GB alone.
- **Fewer with-functions, smaller interfaces.** Each `with` creates an
  auxiliary function whose type carries the abstracted goal; deep chains
  of them are serialised into the interface and loaded by every
  importer. Compacting `Amalgamation`'s chains (above) cut the time its
  profile attributes to no definition, writing the interface included,
  by a third.

## What did not help

- **Matching the indices of Clément's tree checks.**
  `Real-Clifford+CH-TwoLevel-Clement/Hard` (48 s) spends 32 s in
  `nf38-thm` and 8 s in `top-thm`, each passing a generated check
  (`TreeNF38.t38-ok`, `TreeTop.top-ok`, decided there by `refl` in 18 s
  and 8.5 s) to `Main.sound`: the check is run again. Leaving the two
  indices to inference, and then writing them identically on both sides
  (the generator stating `-ok` at `NFData.ic (nfData nf38)` and at
  `zero (suc zero)`, `Hard`'s `g0`…`g3` made patterns), changed nothing
  (48.8 → 48.2 s). The remaining difference is `checkT` itself: each
  tree module writes `open Checker nfData (λ _ → false) using (checkT)`,
  and `Main.sound`'s type names `Main`'s own `open Checker nfData allow`
  — two module-application copies, unfolded and then evaluated to
  compare. The fix would state `sound` and the `-ok` lemmas over the
  original `Checker.checkT` applied to its arguments, or make `checkT`
  opaque with `unfolding` where it must compute; not attempted.
- **One shared width for Real-Clifford+CH's Appendix A modules.**
  `Auxiliary/Move`'s `conj` takes 21 s, and splitting it into four steps
  with explicit types put the cost in the steps whose two sides spell
  the hidden width of `_⊙_` differently — nineteen modules each define
  their own `n = ₃₊ m` (`Move`'s, `A6`'s for `Mpair`, `SPMatrix`'s for
  `spOp`, `Eq65`'s for `Pair`), and `_≐_` unfolds to a Π-type, so two
  products are compared by expanding their sums. Writing the where-module
  copies `T.x` as `E65.Tuple.x args` changed nothing (21.9 → 20.8 s).
  Taking `n` from `SPMatrix` in `Move` alone made `pull-pair` 1.1 → 13 s
  and left `conj` as it was. A module `Auxiliary/Width` that all nineteen
  imported made `Eq65` 19.6 → 595 s: the modules below them (`SigmaPerm`,
  `SignedPerm`, …) spell the width yet otherwise, and the new spelling
  mismatched those in more places than the old ones did. Reverted. A
  spelling has to be shared by everything a comparison reaches, down to
  the bottom of the development, or the change can only move the cost.
- **Returning the rebuilt list from `Rewriting.Step.multistep`.** The fix
  that made `Presentation/Tactics/Words`' loops linear (see `CLAUDE.md`)
  made no measurable difference to `Presentation/Tactic/Rewriting`'s
  users: the duplication it removes bites only under `--call-by-name`.
- **Splitting a step function into named pieces** so that another module
  can reuse them: each function pays its own coverage and case-tree cost,
  which ate the saving (+2 s on `Powers` for −4 s on `Swap`).
- **Hoisting only the cheap module applications** (`Powers`: 6 %).
- **A boolean that builds proofs.** Comparing the coset normal forms of
  `Clifford+CS-3qubit/Step4/Main` by `isJust (nf w =m? nf v) ≡ true`
  rather than `auto : nf w ≡ nf v` made it slower, 55 → 101 s: `_=m?_`
  returns `Maybe (x ≡ y)` and builds an equality proof per element. The
  boolean trick pays only when the boolean is cheap (`eqM`'s `_≡ᵇ_` on
  residues).

## Known costs without a cheap fix

- **Rewrite-step functions over width-indexed generators.** Under
  `--cubical-compatible`, each clause of a step function matching long
  lists of `Gen (₁₊ n)` patterns costs about 0.5 s (`Powers` checks in
  7 s under `--without-K` and 14 s under `--cubical-compatible`; its
  importers need the latter). Removing it would mean step functions over
  a non-indexed representation of the generators.
- **The TopPad equivalences** (`*/TopPad.agda`, generated; nothing
  imports them) spend their time in the reflection macro `⇓-same` of
  `Circuit/TopPad/Closed`: in Figure1's, `Typing.Reflection` is 43 of
  56 s, about 0.7 s per call. Not the final `unify` of the generated
  proof (dropping it saves nothing), and not much the per-node
  `inferType` that checks a definition is a word (dropping it: −16 %);
  `--lossy-unification` does nothing, and `Eq.refl` in place of the
  macro fails at the first power with a symbolic exponent. The likely
  cost is the traversal's fallback to unrestricted `reduce` on word
  definitions the restricted unfolding cannot open; not pursued.
- **Tactic-generated proofs and `--lossy-unification`.** Bian and
  Selinger's ports (`Clifford+CS-3qubit`, `Clifford+T-2qubit`) fail
  under the flag: their tactics take `auto : nf w ≡ nf v` with `w`, `v`
  implicit, and lossy unification solves `w := v`. Binding the words
  (`hypB {u} {t} ax = … {simple-of-gen-star u} {simple-of-gen-star t}
  auto`) makes `Step4/Main` check with the flag, but no faster (52 s):
  their time is the normal-form computation itself.
- **Diffuse cost.** `Paper-V0/Lemmas` (≈21 s) spends its time over
  hundreds of explicit reasoning steps, no definition more than 2.5 s.
  Splitting such a file at its natural module boundaries, with the old
  module kept as a re-export, brings each file under the target without
  reducing the total.
