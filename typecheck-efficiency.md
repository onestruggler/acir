# Typechecking efficiency

What has made modules of this library check faster, what did not, and how
to measure. The target is every module under 20 s of its own checking
time, with 30–40 s acceptable for large modules. Developments with their
own performance notes (Real-Clifford+CH's stored-matrix evaluations, the
abstract readings `⟦_⟧ₒ`, CNOT+Dihedral's tables, …) keep them in
`CLAUDE.md`; this file collects the general techniques.

## Where things stand

A from-scratch timing of every module at c93c2201 (188 minutes, with
other Agda jobs on the machine) checked 1394 of 1405; the 11 failures
are the files already failing (S3xC5's two, `Clifford/Qubit/Selinger/
Placed` and the two modules it blocks — the folder has since been removed — six stale `vqupit` slide files).
Against the run at e56e9fbc the summed module time went 6718 → 4119 s
and the modules over 20 s 53 → 32.

Since then, every one of those 32 has been looked at again, per
definition and per phase, and all but six are under 20 s: the TopPad
equivalences (macro and generator, 359 → 131 s in all), the tactic
ports (`Clifford+CS-3qubit` Step4's `hypB` and Soundness, Step3's
PD4 and PD6, `Clifford+T-2qubit` Equations 43, 44 and 46, split into
modules of 9–20 s), `DecodingChecks` and `Checks8`'s R34 and R42
(split), and `Diamond`, `Auxiliary/Move`, `Eq65`, `Auxiliary/Soundness`,
`Independence/Clifford+CS/Bridge`, `Lemma88/Easy` and `LemmaA1/Base`
and `More` (one cause each, now under 10 s). Four of those last were
first counted as spread. Left at 20–27 s: `Paper-V0/Lemmas` (spread
over 4754 lines; a split would recheck `Qupit-Clifford` under the
root), `Weyl` (evaluation), `TreeNF38` (one generated check),
`U33Di` and `Amalgamation` (spread). Qupit-Phase-Affine's TopPad, left
there too, is now about 8 s (its shared words through the macro's
lemma table), and Figure 1's two about 6 s.
Wall-clock figures from a chunk the watchdog killed are estimates only
(marked approximate): rechecked alone, four of them were 2–8 s.

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
| Decide a matrix identity as one boolean, not `refl` on tries | `Clifford/Qubit/Model/Gates` (since removed) | 71 → 2.9 s |
| Pass the axiom's own words; compare readings as words | `Clifford/Qubit/Model/Faithful` (since removed); `Real-Clifford+CH/Auxiliary/Soundness` (its literal rules, there with a boolean in place of `refl` on tries) | 1436 → 1.5 s; 20.1 → 2.2 s (`sound` 13 → 0.2 s) |
| Bundle many module parameters into one record | `Qupit-Phase-Affine/Phase/Control` | 26.9 → 5.3 s |
| Decide each distinct generated check once, as a named lemma, its evidence left to `_` rather than `tt` (`tt` made the same boolean evaluate about six times slower) | `Groups/Qutrit-Clifford/Box3` (`scripts/emit3.py`: 4134 two-wire steps, 896 distinct, in `Box3/Steps*`); `Soundness/Checks`, `PauliLocal` (`_` only) | nine parts of 15–25 min each → 43 modules of at most 32 s, about 11 min in all, and with the steps in modules of 1800 letters (`STEP_LETTERS`) the 25 Steps modules of 20–31 s are 42 of at most 14 s, and with six relations a part (`emit3.py 6`) the 18 parts of up to 20 s are 29 of at most 11.4 s; 50 → 9.1 s, 41 → 8.2 s |
| Decide a generated equation between two words on what is left of them once their common prefix and suffix are cut off (the step is then made at an index further on): fewer letters to evaluate, and more steps coincide | `Groups/Qutrit-Clifford/Box3` (`scripts/emit3.py`'s `step`: 896 distinct two-wire steps of 72,162 letters → 626 of 41,186) | `Box3/Steps*` 348 → 194 s (42 modules of at most 14 s → 21 of at most 11.8 s), `Box3` in all 464 → 312 s |
| In a function the evaluator runs on long data, pass a repeated subterm (a projection, a split of the list) to a helper as an argument, which is computed once, rather than writing it at each use; and build lists with an accumulator rather than by appending on the left | `Groups/Qutrit-Clifford/Engine.run` (`run-rw`, `run-at`: `lhs e` was computed three times a step), `Box3/Kit.invList` (`invList xs ++ invT x`, quadratic) | `Box3/Part*` 100 → 49 s (at most 8.2 → 3.5 s); cancelling a word of 400 letters and putting it back 331 ms before |
| Before deciding an equation between two words by evaluation, delete from both the runs that an axiom makes the identity, by the axiom (a cheap derivation on short words), and decide the rest | `Groups/Qutrit-Clifford/Box3` (`scripts/emit3.py`'s `reduce`: H⁴, S³, CZ³, ν⁶ on either wire, 45% of the letters, most of them H, the costliest gate; `Box3/Sem*` the equations decided, `Box3/Steps*` the derivations) | 626 equations of 36,804 letters → 506 of 18,972; `Box3/Steps*` 185 s → `Sem*` 106 s and `Steps*` 3 s, `Box3` 234 → 168 s |
| Evaluate a frequent pair of letters as one cheaper operation, proved equal to the two (an identity on coefficients, by the solver over the step written generically) | `Groups/Qutrit-Clifford/Evaluation` (`evL`, `runL`, `applyR2`, `hh-ok`: H H as −3 times a permutation of rows; `Box3/Kit.semℓ` decides by it) | `Box3/Sem*` 106 → 68 s, `Evaluation` 11 → 14.5 s; the folder 324 → 289 s |
| Rewrite a long word as a zipper (the letters before the focus reversed, and the rest), so that a rewrite at an index costs the distance from the last one rather than the index | `Groups/Qutrit-Clifford/Engine` (`Zip`, `moveTo`, `runZ`; the box relations' derivations rewrite at index 870 on average, 87 from the step before) | `Box3/Part*` 49 → 32 s (at most 3.5 → 2.1 s); the folder 289 → 269 s |
| Certify a homomorphism on the basic generators only and carry it to the others along a conjugation that both readings respect, rather than certifying each generator | `Groups/CCX+HH-3qubit/Repaired/DecodingMatrices` (the decoding's matrices: 9 certificates and 41 evaluations, then `Conjugation.decompose`, after CCX+HH-3qubit-opus's `dec-sem`; its step lemmas spell the words out in their types and proofs alike: a `where`-abbreviation on one side made Agda compare two spellings of a matrix reading by unfolding it, 10.4 → 1.0 s) | 106 certificates and 763 evaluations about 100 s → about 7 s; the directory 333 → 198 modules, its module time 195 → 99 s, `Theorems` 195 → 94 s |
| Prove a family of relation instances once, at symbolic indices, by a frame lemma — a centre conjugated by a permutation depends only on where the permutation sends the centre's states, the generators above them commuting with the centre — rather than each finite instance by a certificate of its own | `Groups/CCX+HH-3qubit/TwoLevel` (`Symmetric/CoxeterFrames`, after CCX+HH-3qubit-opus's `Decode`: 21 relation families in place of 2,123 instances, their dispatchers and some 2,000 frame moves and permutation checks; FrameWords' tables met by one evaluated check each) | the directory 910 → 333 modules, its module time 624 → 195 s (the transport layer about 440 s → 3 s), `check.sh` about 12 → under 5 minutes, `Theorems` 649 → 195 s, peak 6.2 → 3.8 GB |
| After a rewrite step, put in canonical form (modulo commuting letters) only the part of the word before its common suffix with the word before the step: a suffix of a canonical form is canonical, so inserting the changed letters into it gives the same canonical form as sorting the whole word | `Presentation/Tactics/Words` (`Commuting.restandardize`, `Rewriting.Step-With-Restandardization`, `Basis-Change-With-Restandardization`); every `comm-canonical` instance of `Clifford+CS-3qubit` and `Clifford+T-2qubit` (`eq-gen`, `same`: the test only finds the suffix) | `Clifford+CS-3qubit` 343 → 246 s (`Soundness/Long1` 15.8 → 4.2 s, `Step4/HypB3` 13.5 → 9.6 s, no module slower); `Clifford+T-2qubit` 142 → 134 s (its slow `Equation*` modules rewrite with `Rewriting.Step`, which sorts by rewrite steps) |
| Decide an equation that a normaliser settles by comparing the two computed normal forms by one boolean, not by `refl` on each computed component (which compares them entry by entry, reducing the words behind them again for each) | `Groups/Real-Clifford+CH/Auxiliary/FrameNorm` (`by-normᵇ`, `cmpNF`) and `Template` (`A5-tmplᵇ`, `tab-eq`): 58 calls in `Frame`, `Eq80`, `ItemB`, `ItemBd3`, `ItemBd4`, `SignSym`, `Twist` | their definitions 23.5 → 15.8 s (`Frame` 10.9 → 7.9 s, `ItemBd4` 3.5 → 1.7 s) |
| Decide a family of generated words on the few pieces they are made of: prove once, generically, that each word is a product of named pieces (its skeleton), read every piece once as a ProdEval factor, and compare products of the pieces' matrices | `Groups/Real-Clifford+CH/Auxiliary/DecodingChecks` (`DecodingChecks/Atoms`: a Hadamard-free letter of Definition 8.3 decodes to a word in 21 multi-controlled gates, at every width) | the 512 signed exchanges 8 × 12.5 s → 7.1 s in one module, the sign pairs 3.1 → 0.5 s; the module and its eight parts about 105 s → about 12 s |
| Compare two stored readings at the difference of their powers of √2, on the row tries themselves, and write constant tries (the identity) out: `scaleM` and `idM` rebuild a matrix entry by entry through trie lookups, which costs more than a few row operations | `Groups/Real-Clifford+CH/Auxiliary/Checks8/Base` (`cmpR`, `I₃`; used by `decide` and DecodingChecks' decisions) | Checks8 about 65 → 31 s (`R34` 16 → 4.5 s, `R42` 15.6 → 11 s, `H01`…`H67` 19.5 → 12.3 s) |
| Merge thousands of one-definition generated modules into chunk modules, each definition a nested module under its old name, and have their users import them from their chunk (`open import … using (module N)`): Agda pays for a module apart from its contents — loading it, merging it into each importer's state, an interface of its own | `Groups/CCX+HH-3qubit` (`tools/bundle.py`, run after the generators: 7548 certificates in 187 chunks, the directory 8279 → 910 modules) | 606 frame certificates checked from scratch 37.7 → 26.1 s, loaded 24.6 → 14.2 s; `check.sh`'s roots (140) 4646 → 2927 s, `TwoLevelScaled`/`Presentation`/`Theorems` about 180 → 61 s each, `TwoLevel` 148 → 33 s, `TransportCaseChecks` 127 → 14 s, peak 5.9 → 5.0 GB, interfaces 350 → 280 MB |
| Check a development through the few roots that reach all of it, not each part as a root of its own: a process per root loads the same interfaces again | `Groups/CCX+HH-3qubit/tools/check.sh` (`CircuitLemmas`, `MissingK`, `Theorems` and four audits, in place of some 200 roots: the relation families, the 106 decoding certificates, the Hadamard relations, the evaluation chunks) | the directory from scratch in 739 s (`Theorems` 649 s, peak 6.2 GB), where the old roots took an estimated 4916 s with the chunks and 7077 s before |
| Take apart a pair computed from permutations by projections in a `where`, not by `with`: with-abstraction abstracts it over the goal, which Agda normalises | `Groups/Real-Clifford+CH/GeneralN/LocalPlace` (`lift0′`, `lift-k`, `place-eq`) | typing 12.7 → 0.13 s |
| State a helper's result in the exact spelling of the record fields it fills (`Base46At.lift u m′` at `₄₊ m′`, not `u ↓ᵏ m′` at `4 + m′`) | `Groups/Real-Clifford+CH/GeneralN/Canon46b` (`evL` for `b46`) | `b46` 9.5 s → below the profiler's threshold |
| Make a wrapper opaque when lemmas about it are matched against goals that differ only inside its arguments: Agda then compares the arguments instead of unfolding the wrapper on both sides (`opaque`, and `unfolding` where its definition is needed) | `Groups/Real-Clifford+CH/GeneralN/Gadget322` (`Step.pc`, a placed colouring; `letter`) | `Step.letter` 5.8 s → below the threshold |
| Write generated derivations without parentheses: letter lists as strings decoded by evaluation (`ℓ "IC…"`), each kind of step a function of its index and strings (`rwˢ k e` for `rw k (sym⁼ e)`) — the operator parser spends time in proportion to the names in scope on every parenthesised subterm | `Groups/Qutrit-Clifford/Letters`, `Box2` (`scripts/emit2.py`), `Box3` (`emit3.py`, `Box3/Kit`) | `Box2.agda` 234 → 26 s (parsing 95 → 4 s, interface 14 MB → small), Box2 with its parts 621 → 163 s; Box3 655 → 475 s, peak 5.5 → 1.5 GB; the folder about 3½ h → 12 min |
| Sparse stored products: rows as combinations of rows, no ring operation on 0 or 1 | `Independence/Semantics/Operators`, `Scaled` (all fragments): `Qutrit-Clifford/Semantics`, `Clifford+CS/Semantics`, `Clifford+T/Semantics`, `Clifford+CS/Projective`, `Clifford+CS/Encodings`, `Qutrit-Clifford/Encoding` | 139 → 18.4 s, 63.8 → 22.9 s, 35.2 → 15.8 s, 23.4 → 14.1 s, 46.7 → 33.4 s, 20.9 → 4.0 s |
| Decide a matrix identity as one boolean, not `refl` on the matrices | `Independence/Clifford+CS/Encodings` (32 gate tables over 𝔻[ω]) | 33.4 → 14.4 s (and its client `Clifford+CS/Completeness` 31.6 → 1.8 s after this and the sparse products) |
| A lemma restated at the goal's width, over a word given by an equation | `Independence/Clifford/Bridge`, `Real-Clifford/Bridge` | 51.3 → 6.4 s, 45.5 → 5.4 s |
| Decide an action's instances by one boolean on closed data, not `Eq.refl` per instance | `ProjectiveClifford/Qubit/Selinger/Soundness` | 344 → 3.3 s (+ 1.7 s in the new `LongRelations`) |
| A pair equation's component proved once over variable words, not `Eq.cong proj₁ e` at particular words | `Independence/Qutrit-Clifford/V0Mat` | 149.6 → 8.2 s (1.57 → 1.06 GB) |
| A function of a three-element type as the table of its values, not a computed power; an enumeration read back over variables, not under as-patterns | `Independence/Qutrit-Clifford/Weyl`, `Faithful` | 37.8 → 25.1 s (1.46 → 0.88 GB), 60.9 → 24.3 s |
| A generated `refl` check stated over the original definition (not a module-application copy) at the very arguments its user passes | `Real-Clifford+CH-TwoLevel-Clement/Hard` | 48.8 → 9.2 s |
| A `T b` proof left to a metavariable (`_`, solved by eta), or a check proved by `refl` on `≡ true`, not `tt` | `Independence/*/Semantics`, the three `Projective`s, `Clifford+CS/Encodings`; `Qutrit-Clifford/Faithful` | 21.0 → 3.9 s, 21.1 → 3.9 s, 15.2 → 3.3 s, 15.1 → 4.1 s, 14.2 → 3.2 s, … (133 → 52 s over eleven modules); 28.5 → 20.1 s |
| A lemma about a concrete word's operator proved over a variable word, the word's facts as hypotheses, then instantiated | `Real-Clifford+CH/Auxiliary/Move`, `Eq65` | 32.8 → 6.8 s, 23.1 → 5.4 s (`conj` 26.5 → 2.8 s, `Σ-conj` 17.5 → 1.9 s) |
| A definitional step stated as a lemma in the defining module's own spelling of a hidden width, and clients going through it | `Real-Clifford+CH/Decoding.dP-HH`, `Lemma88/Easy` | 33.2 → 8.8 s (profile total 47.0 → 19.8 s) |
| A reflection macro that asks no more of the type checker than it needs (no `inferType` on terms whose type it knows), tries `Eq.refl` before its traversal, and is called once per equation (a lemma whose type is computed from the rule, used twice) | `Circuit/TopPad/Closed`, `Circuit/TopPad/gen/gen_toppad.py`: the thirteen TopPad modules that use `⇓-same` | about 359 → 291 → 200 → 131 s in all; Qupit-Phase-Affine 49.0 → 21.0 s, Figure1 48.9 → 19.6 s, Figure1-MS 48.2 → 19.3 s, Simplified-V1 32.7 → 11.0 s, Paper-V0 26.5 → 7.8 s |
| A scaling by √2 as its own operation, not through the general ℤ[√2] product (one integer operation where that spends seven) | `Real-Clifford+CH/Evaluation`, through `Semantics/Ring`'s `√2*`: `Auxiliary/DecodingChecks` | 201 → 169.5 s (reading a decoded letter a fifth faster) |
| A function's costly clauses made lemmas in modules of their own, each typed by a function of the clause's constructor (`Goal r`), the clauses pointing at them; split by estimated cost, not count | `Clifford+CS-3qubit/Step4/Main` (`hypB`, 3192 clauses): `Step4/HypB1`…`HypB5`, `Step4/Simple`; `Clifford+CS-3qubit/Soundness`: `Soundness/Long1`, `Long2` | 57 s → Main 14.6 s and five modules of 8.6–14.1 s (69 s in all); 24 s → 1.2 + 13.4 + 7.2 s |
| A module application restricted to the names its user takes (`module X = M args using (…)`) | `Amalgamations/U33Di` (`DD`, `AAT`, `myANF`) | 23.0 → 20.5 s |
| A table of a function by cases split by its first argument: one function per value, in a few modules, and the table a dispatcher | `Clifford+CS-3qubit/Step3/PD4` (`p105-act`, 1470 clauses), `PD6` (`K0QD-act`, 1701) | 38.4 → 10.6 + 10.1 + 0.2 s, about 50 → 8.9 + 10.7 + 10.2 + 0.2 s (less in all: checking one function of so many clauses was superlinear) |
| An equational chain with its lines written out cut in two at a line, the second part in a module of its own | `Clifford+T-2qubit/Equations/Equation43`, `44`, `46` (with `43b`, `44b`, `46b`) | 48.4 → 17.7 + 18.8 s, 41.4 → 19.0 + 18.6 s, 37.3 → 18.9 + 19.5 s |
| A decision too long for one file split by its outermost quantifier, a module per instance | `Real-Clifford+CH/Auxiliary/DecodingChecks`: `DecodingChecks/ZX0`…`ZX7` (since merged back: the letters are decided on their atoms, below); `Checks8/R34`, `R42` (with `R34Hi`, `R42Hi`) | 169.5 s in one module → ten modules, 19.7 s at most; 23.6 s → 10.1 + 9.8 s, 21.0 s → 9.0 + 9.5 s |
| A chain's index after a step is a function application holding the previous index once, not an expression holding it twice | `Real-Clifford+CH/Auxiliary/SegChain`: `LemmaA1/Base`, `LemmaA1/More` | 23.5 → 0.7 s, 26.4 → 0.1 s |
| A where-function's result type written out, not left as `_` | `Independence/Clifford+CS/Bridge` | 24.0 → 1.2 s (`split` 19.8 → 0.06 s) |
| A where block full of module applications made a parameterised module, the function a one-line call into it | `Real-Clifford+CH-TwoLevel/Diamond` | 23.6 → 8.9 s (Positivity 12.1 → 0.15 s) |
| Letters of generated derivations as definitions at a fixed width, not patterns | `Real-Clifford/Relations/Derived`, `Qubit-Clifford/Relations/Rules/Figure5`, `Figure7` | 44.6 → 14.7 s (0.8 GB), 22.5 → 7.9 s, 22.8 → 9.2 s |
| `Eq.cong₂ f eA eB` given its implicit arguments when f reduces (`mulM`): the expected type is compared with `f ?x ?u` before the arguments are checked, which unfolds both sides | `CCX+HH-3qubit` matrix evaluations (`MissingK/Evaluations`, `Evaluation`, `FrameEvaluation`; `tools/generate*.py`) | MissingK's E04 41.3 → 12.6 s (its checking 32.7 → 1.3 s); the fifteen such modules 21–38 s → 3–4 s |
| Generated certificates import a slim re-export module restricted to the names each uses (`import Kit as K using (…)`, then `open K`), not the four modules whose names they take | `CCX+HH-3qubit` (7548 certificates; `Kit`, `FrameKit`, `generate.py`'s `kit`) | a one-line certificate's interface 52.7 → 9.2 kB; the folder's interfaces 595 → 350 MB; the heaviest root (`DyadicCompleteness`) 9.5 → 6.2 GB |
| Matrix literals in chunks that import from each other only the names they use, rather than one module of a thousand names or a chain of public re-exports | `CCX+HH-3qubit/Evaluation`, `FrameEvaluation`, `MissingK/Evaluations` (`evaluation_chunks`) | `Evaluation` 79.7 s (operator parsing 27 s of it) → twelve chunks of 1.0–1.5 s; `FrameEvaluation`'s chunks 5.7–13.7 s → at most 1.2 s |
| Identities of 8 × 8 matrices over 𝔻 or ℤ[1/√2] (EucDomain's `Matrix`, vectors of vectors) decided by one boolean (`Decide.eqM`, from `_≟ᴰ_` on the entries) rather than `refl`; the costly ones as lemmas in modules of their own | `CCX+HH-3qubit-opus`: `Soundness` (Figure 7 in `Soundness/Figure7a`, `Figure7b`), `TableMatrices`, `Independence` and `PushMatrices` (`gen/mk_indep.py`, `gen/mk_push.py`), `SoundnessH` | 101.8 s → 2.0 + 0.8 + 11.4 s, 81.2 → 15.8 s, 42.7 → 6.3 s, 17.7 → 2.7 s |
| A constructor's implicit indices given (`trK {i₀ = # 0} {i₁ = # 1} …`) when the only argument that fixes them is an equation `act (frame ts D) i ≡ a`: left to unification, the comparison reduces the frame of the symbolic states ts, which grows with their number | `CCX+HH-3qubit-opus/Decode` (`dec-ax`: (2f) and (6a), on eight states) | 94 → 6.7 s ((2f) 24 → 0.2 s) |
| A reflection macro given lemmas for the words several of its goals share, so that its traversal stops at them rather than going through their definitions in every goal | `Circuit/TopPad/Closed` (`⇓-same-by`; a tabled word stays folded), `Qupit-Phase-Affine/TopPad` (`CZ-⇓`, `CS-⇓`, `CCZ-⇓`, from `toppad_configs.py`), Figure 1's two (`M-⇓`, `SWAP-⇓`) | 27 → 10.1 s loaded (about 21 → 8 s), its costliest rule side 4.7 → 0.25 s; Figure 1's 29.3 → 10.0 s and 32.0 → 9.9 s loaded (about 19.5 → 6 s each) |
| Generated lemma modules that import from each earlier part only the lemmas they use (`import … as Pj using (…)`, then `open Pj`), not a chain of public re-exports, and so can be smaller; a record's long derivations in modules of their own | `Qutrit-Clifford/Box2` (`scripts/br2gen.py emit 1000`: `Box2/Part1`–`Part11`, `Box2/Relations1`–`3`) | six parts of 21–64 s and `Box2` 45 s → fourteen modules of 18.5 s at most, Box2 in all 263 → 181 s, the folder's peak 1.13 → 0.76 GB (one loaded session; halving the parts alone, still chained, made the total 357 s) |
| A heavy import that a proof uses through one lemma made a module parameter, its one client applying it | `CCX+HH-3qubit/HadamardRelations` (`Repaired/Even.FromEven`, applied in `Repaired/TwoLevelScaled`) | each loads about 1100 interfaces, not 7900: a batch of three 3.5–4.5 min → 49–99 s, peak 6.0–6.9 → 2.7–3.2 GB |
| A dispatcher of some 700 clauses split by its first argument, one module per value (each clause's right-hand side costs some 70 ms, its type matching the certificate's only after reduction) | `CCX+HH-3qubit/Repaired/DecodingMatrices` (`dyadic-letter`; `Repaired/DecodingLetters/K0`…`K7`); the four-index transport dispatchers (`TransportChunks/r1c`, `r2a`, `r4a`–`r4c`) | 41.8 s → 0.1 s and eight modules of 15.7 s at most; `Transport/r2a` 23.7 s → eight modules of 7.3 s at most |

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
- **Write a where-function's result type out.** `ViaS.transfer` in
  `Independence/Clifford+CS/Bridge` ends in a case split on a parity
  through a where-bound `split`, typed `… → _` so that its result type
  would be read off the use. Each clause was then elaborated against a
  metavariable: a tuple whose components have dependent types, and
  `mapι-injective`'s implicit matrices, inferred without an expected
  type. That took 19.8 s, and the same signature with `transfer`'s
  Σ-type written out takes 0.06 s.
- **A lemma over a variable word.** Operators are functions, so where
  two operator terms are not syntactically equal the conversion checker
  η-expands them and unfolds `⊙` into its sum. Over a variable word `X`
  that stops at `sp X`. Over a concrete word, such as Definition E.1's
  `T.Σw` from a module application in a where block, it goes on to
  evaluate the word's signed permutation, letter by letter. In
  `Real-Clifford+CH/Auxiliary/Move`, `hh-conj`'s matrix step `conj`
  took 26.5 s at `T.Σw`, though the same chain of `≐-trans` steps with
  a variable word took about 1.5 s. The source of the mismatch was never
  found (pinning every hidden width did not remove it). It did not need
  to be: the step is now a top-level `conj-gen` over variable words `S
  S′`, taking the one fact about them it uses (`T.Σ-conj`) as a
  hypothesis, and `conj` is `conj-gen u u′ T.Σw T.Σ′w … T.Σ-conj`
  (2.0 + 0.75 s). `Eq65.Tuple.Σ-conj` was the same case (17.5 s); its
  proof became a private module `Std` over words `X X′`, taking the
  permutation's values and signs at the four indices as parameters,
  and `Σ-conj` its instance (1.2 + 0.7 s). Abstract the term rather
  than compute with it.
- **Positivity checking of a where block.** A where block is checked with
  the clause it belongs to, and Agda runs the positivity checker once
  over everything that block defines, the copies its module applications
  make included. `Real-Clifford+CH-TwoLevel/Diamond`'s `diamond` had a
  where block that opened one module and applied seven (`Route` twice
  with cases of each, `State`, `Trick` three times), and
  `--profile=internal` put 12–14 s of its 24 s in `Positivity`, no
  definition over 1 s. Bisecting with truncated copies ruled out the rest
  of the file, and hiding names from the `open` took only 2.6 s off.
  Turning the block into a module parameterised by the function's
  arguments (`module Diamond-at {a b c d} (ab : a < b) … where`, the body
  unchanged) and defining the function as a call into it (`diamond ab …
  = Diamond-at.result ab …`) took Positivity to 0.15 s and the module to
  8.9 s, its importers unchanged. Look at `Positivity` in the phases
  before restructuring anything else this way.
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
  into the equation (`Clifford/Qubit/Model/Decide`, since removed, after
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
- **Indices that double.** `SegChain`'s chains of segment
  replacements, `at k n ys e ▸ …`, typed each step's successor as
  `Chain (next s) zs`, with `next` a function of the step record `s`.
  So the index of the next step held the previous index twice: as
  `next`'s implicit argument, and inside the proof `e`, whose implicit
  arguments (`sym`'s endpoints, say) had been solved from its type
  `⟪ take n (drop k xs) ⟫ ≈ ⟪ ys ⟫`. A chain of k steps then has
  indices of size 2^k as trees. Agda keeps them shared in memory, but
  positivity checking, dead-code analysis, projection-likeness and the
  occurs check traverse them as trees. `LemmaA1/More`, two lemmas, one
  of them a single chain of 13 steps, spent 6.0 s in Positivity, 3.5 s
  in dead code and 2.9 s in coverage; cutting the chain in two by hand
  took it from 32.5 s to 6.6 s. The fix is in SegChain: the successor
  index is `next k n ys xs`, with `next` a function of the step's data
  and the previous word, so it holds the previous word once and the
  proof not at all (`Step xs k n ys` carries the data in its type, and
  `at` builds it). The unfolded `take k xs ++ ys ++ drop (k + n) xs`
  would hold it twice again. Base 23.5 → 0.7 s, More 26.4 → 0.1 s, with
  the generated files unchanged. Look for this wherever a data type's
  index after a step is computed from the step.
- **A definitional step, stated where it is defined.** `Lemma88/Easy`
  proves its Hadamard rules through the decoding of a letter,
  `dP (HH a b c d _ _) = dHH (toℕ a) …`. Unfolding that clause gives
  `toℕ {2 ^ n} a` with Decoding's private `n`, while `toℕ a` written in
  Easy is `toℕ {2 ^ N} a` with Easy's own `N`. Both are `₃₊ m`, but the
  terms are never syntactically equal, so every comparison of the two
  readings reduced `dHH` on both sides — the `if` on `distinct4`, the
  free-index search, `hpat` on the Gray codes — and compared the results,
  level after level. `dP (HH …) ≡ dHH (toℕ a) …` by `refl` took 4.7 s in
  Easy, too little to measure in Decoding. `Decoding.dP-HH` states the
  step there, for any naturals equal to the indices, and Easy goes
  through it, so the only comparison across the two spellings is `toℕ a`
  against `toℕ a`. In e42 the left side went 14.5 → 0.2 s, e35 7.0 →
  0.4 s, and the module's profile total 47.0 → 19.8 s. The sign was that
  splitting the slow proof into named steps left every step cheap: the
  cost was in the joins between them. One join is left in `d-hh0132`
  (4 s), between `HH {N}` and `HH {n}`; removing it would take one
  definition of the width shared by both modules, which the shared-width
  attempt below warns against.
- **`Eq.cong proj₁` at a particular word compares the whole pair.**
  `Independence/Qutrit-Clifford/V0Mat` (149.6 s) carried the Pauli
  component of the semidirect product's law through `Eq.cong proj₁
  (∙ˢᵈ x y)`, once at the particular words `Z^ -1/2` and `S`. The
  endpoints are then solved against the goal at the pair type, so the
  two readings of the word are compared symplectic part and all: the
  pitfall `CLAUDE.md` records for `Qupit-Clifford/SemShift`. The same
  fix works: `∙ˢᵈ₁ x y = Eq.cong proj₁ (∙ˢᵈ x y)` proved once over
  variable words, used at the four places — 8.2 s.
- **A small function as its table.** Qutrit-Clifford's `ω^ a` was
  `x ^ (4 * toℕ a)`, up to eight products in ℤ[ζ₁₂] each time it is
  evaluated, and `Faithful`'s `all-ok₁` evaluates it thousands of times
  deciding that the one-qutrit Weyl operators are distinct (729 pairs).
  As the table of its three values, with `ω^-x` for the one module
  (`Weyl`'s `Decide₁`/`Decide₂`) that needs it as a power of x because
  `eqₖ` reads phases so, `Weyl` went 37.8 → 25.1 s (1.46 → 0.88 GB). In
  the same module `core₁` read `all-ok₁` back under the patterns
  `p@(a , b)`, which instantiate the enumerator's lambdas at pairs, where
  `ok₁` unfolds (16 s in the profile); one lemma `ok₁-all` over
  variables does it instead. With `emb-pow` given the operator as the
  terms around it spell it (`ix (proj₂ Hᵍ)`, not a private alias `Hm`),
  `Faithful` went 60.9 → 24.3 s.
- **Prove a boolean check by `refl` on `≡ true` or by `_`, never by
  `tt`.** The same evaluation — Weyl's two-qutrit check, 81 pairs of
  9 × 9 products — cost, by how it was proved:

  | Proof | Time |
  |---|---|
  | `Decide₂.sound … _` (a `T b` argument left to a metavariable) | 11.9 s |
  | `Eq.refl : b ≡ true` | 14.9 s |
  | `pM : T b ; pM = _` (a metavariable at the top level) | 69.8 s |
  | `Decide₂.sound … tt` | 70.6 s |
  | `pG : T b ; pG = tt` | 126.6 s |

  So `tt` checked against `T b` is five to ten times dearer than the
  same `b` evaluated as the type of a metavariable solved by eta for ⊤,
  or compared with `true` for `refl`. Independence's semantics checked
  every axiom as `check 0 refl _ _ tt`; as `check 0 refl _ _ _` the six
  Semantics modules, three Projectives and `Encodings` went 133 → 52 s
  (Qutrit-Clifford's 21.0 → 3.9 s). Where the proof is a whole
  definition, `_` is the middle row; `T`-lemmas from an `≡ true` proved
  by `refl` would be the faster form, and is: `Faithful.all-ok₁` (729
  cases) took 7.5 s as `tt`, 3.6 s as `_` and 0.9 s as `refl` on
  `≡ true`. Read such a check back from the `≡ true` itself, by a lemma
  over an abstract predicate (`all4-sound f e`): written `T-≡ all-ok₁≡`
  at the call site, `T-≡`'s implicit is solved through `T ?b = T (…)`,
  and `T` being a function Agda evaluates the right side, the whole
  check again (`ok₁-all` 5.3 s, then under 0.4 s; `Faithful` 28.5 →
  20.1 s). The rest of the repo already proves its evaluations by
  `refl` on `≡ true` (Real-Clifford+CH's `Same`, `evaluated Eq.refl`).
- **A cost that is neither the evaluation nor the boolean.**
  `Faithful.inv-right₀`'s CZ clause (9.4 s, against 0.9 s for H) is not
  the CZ³ check: split out as its own definition it does not register.
  The goal spells the gate `ix (proj₂ (M₀ (gate₂ CZ-gate)))`, the chain
  `ix (tenM (proj₂ CZᵍ) idM)`, and under `_≐_`, a Π-type, the products
  are fully applied, so the two are compared by unfolding `⊙` into its
  digit sums, ten times larger on 9 × 9 than on 3 × 3. Giving `ix-emb`
  and `ix-M` their widths changed nothing; restating `_≐_` as a record,
  so that operators are compared as arguments, would, at the cost of the
  whole Operators layer.
- **A proof by `refl` is passed on only as the same term.**
  `Real-Clifford+CH-TwoLevel-Clement/Hard` (48.8 s) spent 32 s in
  `nf38-thm` and 8 s in `top-thm`, each passing a generated check
  (`TreeNF38.t38-ok`, `TreeTop.top-ok`, decided by `refl` in 18 s and
  8.5 s) to `Main.sound`, which ran it again. Two things differed. The
  arguments: `Hard` passed `NFData.ic (nfData nf38)` and its own `g0`,
  the trees their private `f2` and `f0`. And the head: each tree module
  wrote `open Checker nfData (λ _ → false) using (checkT)`, `Main.sound`
  named `Main`'s own `open Checker nfData allow`, and a module
  application copies `checkT` under a new name each time. A first
  attempt aligned the arguments only and changed nothing (48.8 → 48.2
  s), since with different heads the syntactic check fails anyway and
  both sides are evaluated. With both aligned it is 9.2 s: `sound` takes
  its check over `Checker.checkT` itself, applied to its arguments (no
  copy), the generator states each `-ok` at exactly the arguments `Hard`
  passes (`NFData.ic (nfData nf38)`, `zero (suc zero)`, `Hard`'s
  `g0`…`g3` made patterns), and the selections are named (`allowNone`,
  `allowAll` in `Tree`) rather than written as a lambda in each place.
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
  6.2 s). It did nothing for `Qupit-Clifford/SemRealises`. A module's
  own peak can be far below what a batch reaches: `Selinger/Translation`
  overflowed 3 GB in a batch that also rechecked other modules, and
  peaks under 1 GB alone.
- **An interface records the scope of every module its module imports.**
  Not only the names it opens: `import M as N` puts the whole of M in
  scope qualified, and the interface keeps that scope (it is what
  reloading the file restores). A module whose only import was `import
  …PE00008 as E` wrote 2.9 kB; adding `open import …Syntactics using
  (_≈_)` made it 20 kB. So `CCX+HH-3qubit`'s 7548 one-line certificates,
  each opening Syntactics, Frames, FrameWords and Engine (which
  re-exports Presentation.Base's congruence), wrote 50–65 kB each, and a
  root that imports them all (`TwoLevel`, `DyadicCompleteness`, the
  presentation) loaded 595 MB of interfaces into 7–9.5 GB. An `import
  Kit as K using (…)` restricts the qualified scope too (`open import
  Kit using (…)` does not: it imports all of Kit, then opens some), so
  each certificate now imports a slim module listing what certificates
  use, with exactly the names it uses, and then `open K`: 9 kB, 350 MB in
  all, 6.2 GB at the heaviest root. A module application inside a
  certificate (`module GL = GLib.Group-Lemmas _===_ grouplike` in 1310 of
  them, for one lemma) is copied into its interface too; apply it once
  in the slim module and re-export the one name.
- **Load less: a heavy import used through one lemma can be a
  parameter.** Each of the nine Hadamard relations of `CCX+HH-3qubit`
  checked a few seconds of proof after loading 7900 interfaces (6–7 GB),
  because it compared even normal forms by dyadic completeness, which
  imports the whole transport development. With that comparison a
  module parameter (its type in the light `Repaired/Even`), each loads
  1100 interfaces and peaks at 3 GB; the one client,
  `Repaired/TwoLevelScaled`, which loads everything anyway, applies them
  (`module C0 = …r7b_i0123 from-even using (proved)`).
- **Fewer with-functions, smaller interfaces.** Each `with` creates an
  auxiliary function whose type carries the abstracted goal; deep chains
  of them are serialised into the interface and loaded by every
  importer. Compacting `Amalgamation`'s chains (above) cut the time its
  profile attributes to no definition, writing the interface included,
  by a third.

## What did not help

- **Two small things in Qutrit-Clifford.** Deciding `Faithful`'s three
  gate powers by `eqWith` instead of `refl` on 3 × 3 tries changed
  nothing measurable (61.3 → 60.9 s; kept, as the house style); naming
  the module argument of `Fwd.Iso.h _` in `V0Mat.law` (it is `n`) left
  that definition at 7 s. `Clifford+CS/ThreeQubit` (27 s in the full
  run) profiles at 20.1 s, of which 17.9 s are miscellaneous (module
  applications, serialisation) and no definition over 0.7 s: nothing to
  fix. And `Faithful.inv-right₀` (10 s) is not its `with` on the
  recursive call: projections instead measured the same back to back
  (30.3/28.0 s against 29.8/28.0 s; reverted). In `Weyl`, deciding
  `Decide₁`/`Decide₂` by `eqWith 1# (ω^ φ)` instead of `eqₖ` (no power
  of x) and building D₂'s table by `tenM` took `local-CZF` 11.2 → 8.8 s
  but `Decide₂`'s where-bound `e` 6.6 → 8.0 s, the module the same
  (reverted); writing the check out in `sound`'s hypothesis instead of
  naming it `ok` made `Weyl` run for over six minutes (stopped).
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
  (What did fix `conj` was to keep the concrete words out of the
  comparison altogether: see "A lemma over a variable word" above.)
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
  `Circuit/TopPad/Closed`: in Paper-V0's, `Typing.Reflection` is 25.7
  of 29.5 s, about 0.37 s per call. The per-node `inferType` that asked
  whether a definition is a word is gone (it always is: the traversal
  only visits words), which took a fifth off every module (Figure1's
  48.9 → 39.1 s, Qupit-Phase-Affine's 49.0 → 35.0 s, the Symplectic ones
  to about 10 s). And the macro now tries `Eq.refl` first, under
  `catchTC`/`noConstraints` and only once the goal has no metavariable
  (unifying with a meta in it could solve the meta): wherever no power
  is stuck the traversal ends in `Eq.refl` anyway, and unification gets
  there without quoting anything (Paper-V0's 21.6 → 10.1 s, all thirteen
  291 → 200 s). And each equation is now proved once: a stuck rule's
  padded form (`r↓`) and `srel-⇓` both needed, from the macro, that each
  side of the rule ⇓'d is the same side one wire wider. The generator now
  emits those as lemmas `r⇓ˡ`, `r⇓ʳ` used by both, their types computed
  from the rule's constructor at the two widths (`⇓ˡ r r′ = w ⇓ ≡ w′`
  for the left sides w, w′ of r and r′), so no word is written out
  (all thirteen 200 → 131 s; Figure1's 31.2 → 19.6 s). What is left
  (Qupit-Phase-Affine's 21.0 s) is rules with stuck powers going through
  the traversal, whose cost is spread over its reduce-and-quote steps. Not the final `unify` of the generated proof
  (dropping it saves nothing), nor the fallback to unrestricted
  `reduce` (dropping it saves nothing on Paper-V0, and Figure1's words
  need it); `--lossy-unification` does nothing, and `Eq.refl` in place
  of the macro fails at the first power with a symbolic exponent. The rules that cost most there shared words
  (CS, CCZ, CZ inside them, CCZ of seventeen factors) whose definitions
  the traversal went through once per rule side; the macro now leaves a
  word folded when it is given a lemma for it (`⇓-same-by`, the table
  Figure 1 already passed for its Legendre symbol), and the generator
  gives Qupit-Phase-Affine `CZ-⇓`, `CS-⇓` and `CCZ-⇓`, each the macro
  once: the rule lemmas went from about 25 s to 7 s in one loaded
  session (the module 27 → 10.1 s; about 21 → 8 s unloaded).
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
