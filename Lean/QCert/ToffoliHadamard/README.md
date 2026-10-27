# Amy, Ross, Wesley (2024): three-qubit Toffoli–Hadamard circuits

M. Amy, N. J. Ross, S. Wesley, *A sound and complete equational theory for
3-qubit Toffoli–Hadamard circuits*, QPL 2024, arXiv:2407.11152.  Formalized
from the paper (TeX source, PDF, and its supplement), numbering as printed.

## Statements (`Theorem.lean`)

* `theorem_5_2 : IsPresentationOf R1 sem1` — `R₁` = Figure 4 (`R₀`,
  (1)–(46)) ∪ Figure 7 (`R₈⁴`, (83)–(101)) ∪ `{(r_K)}` presents `O(8, 𝔻)`
  (`O_ZHalf 8`) on `Σ₁` (Theorem 5.2 **with `(r_K)` restored**).
* `rK_independent : ¬ Derivable Fig47 (w [K12]) (w rKrhs)` and
  `theorem_5_2_as_stated_fails : ¬ IsSubPresentationOf Fig47 sem1` —
  `(r_K)` does not follow from Figures 4 and 7, so Theorem 5.2 as stated
  is false (both sides of `(r_K)` have the same matrix).
* `theorem_6_3 : IsPresentationOf R2 sem2` — `R₂ = R₁ ∪` Figure 8
  ((102)–(108)) presents `TofH(3) = L₈` (the orthogonal matrices `N/√2^k`,
  `N` integral; Li–Ross–Selinger's `L 8`) on `Σ₂ = Σ₁ ∪ {H₂}`
  (Theorem 6.3, with surjectivity).

Reviewer's files: `Syntax.lean` (the alphabets `Sym1`, `Sym2`; Figures 4,
7, 8 and `(r_K)`; the abbreviations of Sections 5.3 and 5.6 for
multi-level operators), `Matrices.lean` (the gates of Section 3 as
operators on `|x₀x₁x₂⟩`), `Semantics.lean` (`sem1`, `sem2`, the target
groups), `Theorem.lean`.

## Conventions

* The alphabet is the paper's, one symbol per gate: `X0 … CCZ`, `Kc` for
  `K_[0,1,2,3]`, `S01` … for `σ_{0,1}` …, `H2`.  Words are read left to
  right as matrix products (`⟦u v⟧ = ⟦u⟧⟦v⟧`).
* Qubit `0` is the most significant: the basis vector of `|x₀x₁x₂⟩` is
  `4x₀ + 2x₁ + x₂` (as the paper's multi-level operators require:
  `CCX_{0,1} = X_[6,7]`, `CCZ = (−1)_[7]`).  In the framework's wire
  numbering (wire 0 the least significant digit) paper qubit `j` is wire
  `2 − j`.
* Matrices are defined over any commutative ring with an element `s` for
  `1/√2` (`Matrices.lean`) and taken over `ℝ` with `s = 1/√2`; identities
  are decided over `ℚ(√2)` (`Eval.lean`: each gate as a row permutation,
  row signs or a dense matrix, so that words of hundreds of letters are
  evaluated quickly by `decide +kernel`).

## Errors in the paper (each checked on matrices; `gen/` scripts in scratch)

* **`(r_K)` is missing** from Theorem 5.2's relations (Figures 4 and 7):
  proved independent (`Independence.lean`): interpret each Toffoli–K gate
  `g` as `R⟦g⟧R` with `R = I − J/4` the reflection in the all-ones vector,
  and `K_[0,1,2,3]`, `CCZ` as themselves; every relation of Figures 4 and 7
  holds (Figure 4 is conjugated by `R`, Figure 7 only involves `K_[0,1,2,3]`,
  `CCZ` and permutation gates, which commute with `R`), while `(r_K)` fails
  (entry `(0,0)`: `−1/4` against `1/2`).
* (33) is printed `CCX_{0,1} ≈ σ_{1,2} CCX_{0,2} σ_{0,2}` (false); used as
  `σ_{1,2} CCX_{0,2} σ_{1,2}`.
* The alias `(−1)_[0] = X₀ X₁ CCZ X₁ X₀` (Section 5.6) is `(−1)_[1]`; used as
  `X₀ X₁ X₂ CCZ X₂ X₁ X₀`.  (With the printed alias (85), (94), (97), (98),
  (101) are false.)
* (97) is printed `X_[0,1] K_[0,1,2,3] ≈ K_[0,1,2,3] X_[0,1] (−1)_[1] (−1)_[3]`
  (false); used as `… ≈ K_[0,1,2,3] X_[1,3] (−1)_[1] (−1)_[3]`, the relation
  (4a) of Li–Ross–Selinger it transcribes.
* (100) is printed `K_[0,1,2,3] K_[1,3,4,5] ≈ K_[1,3,4,5] K_[0,1,2,3]` (false:
  they do not commute); used as `… ≈ K_[2,3,4,5] K_[0,1,2,4]`, the relation
  (5a) of Li–Ross–Selinger.  The same two slips are in Figure 5 ((63),
  (66)), Figure 6 ((78), (81)) and Figure 10 ((125), (128)).
* `(r_CX) : CX_{0,1} ≈ X_[2,6] X_[3,7]` (Section 5.5) is false
  (`X_[2,6] X_[3,7] = CX_{1,0}`; `CX_{0,1} = X_[4,6] X_[5,7]`); it is not part of
  the final presentation.
* The decomposition `CCZ = K_{1,2} CZ_{1,2} X₀ K_[0,1,2,3] X₀ CZ_{1,2}
  K_[0,1,2,3] X_[5,6]` of Section 5.7 is false (the other one,
  `K_[0,1,2,3] = (K_{1,2} CCZ)³ X_[5,6]`, holds); not part of the presentation.
* Section 5.5 says `CCX_{1,2} = X_[6,7]`; it is `CCX_{0,1} = X_[6,7]` (as
  stated in Section 5.0).
* Ambiguity: the abbreviations `X_[1,3]`, `X_[0,4]` (Figure 7) are not
  spelled out; `X_[a,b] = X_[a,a+1] X_[a+1,b] X_[a,a+1]` is used (relation
  (76) generalised).  `K_[a,b,c,d]` and `(−1)_[c]` follow Section 5.3.

## What is proved

* Soundness of `R₁` and `R₂` (`Soundness.lean`), every relation decided on
  `8 × 8` matrices; grouplike (every letter a unit modulo `R₁`).
* Independence of `(r_K)` and the failure of Theorem 5.2 as stated.
* **Section 6** (`Section6.lean`): Lemma 6.1 (`H₂` moves past every letter,
  by Figure 8 and the definitions (1)–(20)), Lemma 6.2 and Theorem 6.3's
  argument (`H₂` is not dyadic), via the generic extension lemma of
  `LiRossSelinger/Extension.lean`: completeness and generation of `R₂` from
  those of `R₁`.
* Generation (surjectivity) of `O(8, 𝔻)` by `Σ₁` (`Encode.lean`), with no
  `sorry`: every generator of Li–Ross–Selinger's `𝒢₈` has the matrix of the
  circuit of the paper's abbreviations (`X_[a,b]`, `(−1)_[a]` decided by the
  kernel; `K_[a,b,c,d]` as `K_[0,1,2,3]` conjugated by four transpositions,
  proved in general), and Li–Ross–Selinger's Theorem 3.5 (proved in
  `LiRossSelinger/Generation.lean`).  Hence `theorem_6_3`'s surjectivity is
  sorry-free too.
* Completeness of `R₁` reduced to Li–Ross–Selinger's completeness at
  `n = 8` (`Translation.complete1_of`), given two families of derivations.
* `Theorem.encodesTable1`: the encoding of every one of the 2123 instances
  of Li–Ross–Selinger's Table 1 at `n = 8` is derivable from `R₁`
  (`Engine`, `Micro`, `Macro`, `Gens`, `MacroTable`, `Transport`,
  `Families`; see "Derivations" below).
* `Theorem.roundTrip`: every letter of `Σ₁` is derivably equal to the
  circuit of its decoding (`RoundTable`, `RoundTrip`).
* Both depend on the axioms `propext` and `Quot.sound` only.  So
  completeness of `R₁` (Theorem 5.2 with `(r_K)`) depends only on
  Li–Ross–Selinger's Theorem 4.10 at `n = 8`.

## Derivations (`encodesTable1`)

* `Engine.lean`: tables of equations replayed by `decide +kernel`, each
  equation proved by packed steps over the earlier ones; plain steps, and,
  when every letter is an involution, rotation steps (an equation `l = r`
  is the relator `l · rev r`; every rotation `u v` of it or of its reverse
  gives the rule `u → rev v`).
* `Micro.lean` (generated): in `R₁` itself, every letter is an involution,
  and the paper's words `xAdj i` for `X_[i,i+1]` satisfy the Coxeter
  relations of `S₈` — 311 derived relations found by a bidirectional
  breadth-first search over rotations of relators; the relations of
  `X_[3,4]` go through `xAdj 3 = P · X_[3,5] · P⁻¹` with `X_[3,5]` a
  three-letter word.
* `Macro.lean`: the alphabet `ML = {T i, N, K}` read through `phi`
  (`T i ↦ xAdj i`, `N ↦` the alias of `(−1)_[0]`, `K ↦ K_[0,1,2,3]`); every
  encoding `enc g` is `phi` of a word, Figure 7 is literally `phi` of
  equations over `ML`, and derivations from the Coxeter relations and
  Figure 7 over `ML` map to derivations in `R₁` (`toR1`).
* `MacroTable.lean` (generated): the complete rewriting system of `S₈`
  (43 rules, Knuth–Bendix), and `T_j · enc g · T_j = enc (s_j g)` for all
  630 pairs of an adjacent transposition and a generator it keeps
  well-formed, by `S₈` normal forms and pushing the stabiliser of `N`
  ((85)–(90)) or `K` ((91)–(93)) across it.
* `Transport.lean`: hence conjugation by the word of a path of valid
  adjacent transpositions renames the indices of a relation; the encoding
  of `X_[a,b]` is the word of the palindromic path of `(a b)`.
* `Families.lean` (generated): (1a), (2a)–(2c), (3a)–(3g) are conjugation by
  `X_[a,b]`; (1b), (1c), (2d)–(2f), (4a)–(4c), (5a) are carried along a
  bubble-sort path from a relation of Figure 7, and (6a) is derived from
  (101); one `decide +kernel` per family checks every instance's path.

## Derivations (`roundTrip`)

* Each letter has a *route* (`Micro.routeLit`): a word equal to it in `R₁`
  made of earlier letters and of the words `xAdj i`, `neg0`, `K_[0,1,2,3]`
  of the macro letters — a definition of Figure 4 (`CZ₀₁ = K₁₂ CX₀₁ K₁₂`,
  …), `(r_K)` for `K₁₂`, the alias of `(−1)_[0]` for `CCZ`, or a short
  derivation (`X₂ = CX₀₂ X₀ CX₀₂ X₀`, `CX₀₂ = X₁ CCX₀₁ X₁ CCX₀₁`,
  `CCX₁₂ = V CCX₀₂ V` with `V = X_[3,5]`, …, found by search) for `X₀, X₁,
  X₂, CX₀₁, CX₀₂, CX₁₀, CCX₀₂, CCX₁₂`.
* `RoundTable.lean` (generated): with each earlier letter replaced by its
  round trip, the route's macro word equals the encoding of the decoding
  over `ML` — `S₈` normal forms for the permutations, the stabiliser of
  `N` pushed across it for `CCZ`, and for `Z₀, Z₁, Z₂, CZ₀₁, CZ₀₂, CZ₁₂,
  K₀₁, K₁₂` derivations in Li–Ross–Selinger's Table 1 (91 instances, read
  over `ML` by `table1_macro`).
* `RoundTrip.lean`: induction along the order of the routes.

Build times (each module on its own, given its imports): `Engine` 7 s,
`Micro` 40–60 s, `Macro` 30 s, `Gens` 8 s, `MacroTable` 2.5 min (up to
8 min on a loaded machine; 630 transport certificates, 30 000 steps),
`Transport` 6 s, `Families` 28 s, `RoundTable` 13 s, `RoundTrip` 6 s.
The derivations are generated by Python and C scripts in the session
scratch (`th/`: `bfs.c`, the searches `sat2.py`, `micro2.py`, `mfacts.py`,
`routes.py`, `rt_lrs.py`, and the emitters `emit_micro.py`,
`emit_macro.py`, `emit_fam.py`, `rt.py`).

## Remaining `sorry`

None in this folder.  Completeness of `R₁` (and so Theorems 5.2 and 6.3)
depends on a `sorry` only through `LiRossSelinger.complete`
(Li–Ross–Selinger's Theorem 4.10, its Main Lemma) at `n = 8`.

Everything else (soundness, independence, Section 6, surjectivity, the
translation of Table 1 and the round trip) is proved.
