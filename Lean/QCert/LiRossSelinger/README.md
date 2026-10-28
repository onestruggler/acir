# Li, Ross, Selinger (2021): `Oₙ(ℤ[1/2])` and `Lₙ`

S. M. Li, N. J. Ross, P. Selinger, *Generators and relations for the group
`Oₙ(ℤ[1/2])`*, QPL 2021, arXiv:2106.01175.  Formalized from the paper
(TeX source and PDF), numbering as printed.

## Statements (`Theorem.lean`)

* `presentation n : IsPresentationOf (Table1 n) (sem n)`: the relations of
  Table 1 present `Oₙ(ℤ[1/2])` on the generators `𝒢ₙ` (Theorems 3.5, 4.3,
  4.10), for every `n`.
* `presentationL m (hm : 1 ≤ m) : IsPresentationOf (Table12 m) (semL m)`:
  for `n = 2m ≥ 2`, Tables 1 and 2 present `Lₙ`, the orthogonal matrices
  `N/√2^k` (`N` integral), on `𝓕ₙ = 𝒢ₙ ∪ {I ⊗ H}` (Theorems 5.4, 5.7).

Reviewer's files: `Syntax.lean` (generators `Gen n`, Table 1 `Table1`,
`GenL`, Table 2 `Table12`), `Semantics.lean` (matrices `X`, `H`, `K` of
Definition 2.4, `genMat` the level matrices of Definition 2.5, the target
groups `O_ZHalf n` and `L n`, `matIH` = `I ⊗ H`), `Theorem.lean`.

## Conventions

* **Indices start at 0** (the paper's at 1): the paper's `X_[a,b]` is
  `Gen.x (a-1) (b-1)`.  Table 1's caption ("indices distinct, relations
  well-formed") is made explicit: every generator has increasing indices,
  and the indices of a relation are distinct (`List.Nodup` hypotheses where
  the order is not forced).  So the renaming relations (3a)–(3g) only move
  an index up (`X_[a,a'] X_[a,b] ≈ X_[a',b] X_[a,a']` with `a < a' < b`).
* `Lₙ` is stated for even `n = m * 2`, `m ≥ 1` (for `n = 0` the word `I⊗H`
  has the value `1` but is not derivably trivial, so completeness fails
  there; the paper says "n even").  Index `t` lies in block `t / 2`, the
  blocks of `I_{n/2} ⊗ H`.
* Words are read left to right as matrix products, `⟦G₁…G_m⟧ = G₁⋯G_m`
  (as in the paper, §4).

## Corrections to the paper

* **Table 2, (7d)** has its exponents exchanged.  As printed (1-based `a`):
  `(I⊗H) X_[a,a+1] (I⊗H) ≈ (−1)_[a+1]^{a+1} X_[a,a+1]^a K_[a−1,a,a+1,a+2]^a`.
  For odd `a` the left-hand side is `(−1)_[a+1]` (the printed right-hand
  side is `X_[a,a+1] K_[a−1,…]`, and for `a = 1` it is not even
  well-formed, `K_[0,1,2,3]`); for even `a` it is `X_[a,a+1]
  K_[a−1,a,a+1,a+2]`.  Checked on matrices for `n = 2, 4, 6, 8`
  (e.g. `n = 4`, 1-based `a = 1`: `(I⊗H) X_[1,2] (I⊗H) = diag(1, −1, 1, 1)
  = (−1)_[2]`).  Used corrected, as the two constructors `r7d_even`
  (0-based even `a`) and `r7d_odd`.
* Definition 5.2 writes `𝓕ₙ = {(−1)_[a], X_[a,b], K_[a,b,c,d], I ⊗ H |
  1 ≤ a, b, c, d ≤ n}` without the order `a < b < c < d` of Definition 2.6;
  the generators of `𝒢ₙ` are used.

## What is proved

* Soundness of Table 1 at every `n` and every choice of indices
  (`Soundness.sound`, Theorem 4.3): moved to its own at most eight indices
  by a level-matrix embedding (`Local.lean`), each relation is an identity
  of rational matrices decided by the kernel (`ListMat.lean`: list
  matrices, products evaluated by `decide +kernel`).  The cases are
  generated (`gen/mk_sound.py`, scratch).
* Soundness of Table 2 at every `m` (`SoundnessL.soundL`, Theorem 5.4):
  conjugation by `I ⊗ H` acts blockwise on block-aligned level matrices
  (`Blocks.ih_conj_levelMat`), so each relation reduces to `2 × 2` or
  `4 × 4` identities over `ℚ(√2)`.
* Grouplike: every generator is an involution ((1a)–(1c), (7a)).
* **Theorem 3.5 (generation)**, `Generation.generation`: the exact synthesis
  algorithm as a column reduction (Lemmas 3.1–3.4: least denominator
  exponent, four odd entries made even by `K (−1)^τ`, unit columns `±e_a`).
* **Lemma 5.5** (`PushL.pushes`): `I ⊗ H` moves past every generator — past
  the basic ones by Table 2, and every generator is a conjugate of basic
  ones by the renaming relations (3b)–(3g) (the paper uses Theorem 4.10 and
  Lemma A.19 here; this route needs no completeness).
* **Corollary 5.6, Theorem 5.7** from Theorem 4.10 (`PushL.completeL_of`,
  `surjectiveL_of`, through the generic `Extension.complete_ext`): every
  word is `w (I⊗H)^b`, and `b` is determined by the matrix since
  `1/√2 ∉ ℤ[1/2]`.
* General lemmas (in this folder, usable elsewhere): `LevelLemmas`
  (`levelMat_comp`, `levelMat_mul`, `levelMat_map`), `ListMat`
  (kernel-evaluable list matrices, sparse row operations `Act`), `Units`
  (grouplike from units, `derivable_map`), `Extension` (adding an
  involution that normalises the words).

## Theorem 4.10: structure of the proof

* `Algorithm.lean`: Algorithm 1 made deterministic (pivot `j` of
  Definition 3.6, least denominator exponent, the first four odd entries,
  the signs `τ`), the level `(j, k, ℓ)` in lexicographic order, and
  `level_next_lt`: each syllable lowers the level.
* `Reduction.lean`: the normal words `nw` (`nw s = nw (N s) · N`) and
  `complete_of`: Theorem 4.10 from two statements, `MainLemmaBasic`
  (Lemma A.20 for the basic edges that do not raise the level) and
  `BasicDecomp` (Lemma A.19 with a level bound at every intermediate state).
  The induction is on the level of the edge, `max (level s) (level (G s))`,
  with basic edges before the others at each level; a basic edge that
  raises the level is closed by the square at its higher endpoint (every
  generator is an involution).

## Gaps in the paper's proof of Theorem 4.10

1. **Lemma A.19** (every simple edge is a sequence of basic edges with the
   same extent and level) is not proved in the paper; it cites Greylyn 2014.
   It is proved here (`Decomp.lemmaA19`).
2. **Retrograde edges.** Lemma A.20 dismisses the cases where `G` acts on
   already fixed columns ("this case is retrograde") without a diagram, but
   the induction of Lemma 4.8 (on `level(s)`) and Lemma A.21 apply the Main
   Lemma to every basic edge at every state, including those.  As written
   the induction does not cover them.  The formalization inducts on the
   edge level instead (above), which needs the Main Lemma only for edges
   that do not raise the level and makes Lemma A.21 (and its "wedge" lemma)
   unnecessary.  (Some raising edges are treated anyway, e.g. `G = K` with
   `a = 1`, `level(r) = (j, k+1, ·)`.)
3. Typos in levels, e.g. "`level(r) = (j,k,m+1)`" in the case
   `|{a,b,c,d} ∩ {1,2,3,4}| = 0`, where four odd entries appear (`m+4`).

* `Decomp.lean`: **Lemma A.19, proved** (`lemmaA19`).  Every generator is
  derivably `P g₀ P⁻¹` with `g₀` basic and `P` adjacent transpositions up
  to its extent (renaming relations (3b)–(3g)); every intermediate state is
  a permutation by `P`'s letters of `s` or of `G s`, which keeps the columns
  beyond `max(j(s), j(G s))` fixed (the extent lies below that) and permutes
  the pivot column, so it never rises above `max(level s, level(G s))`.

* Lemma A.20 (`MainLemma.mainLemmaBasic_cases`), the case distinction of
  Figure 9 of the paper.  The tools:
  * `Square.lean`: a square needs only the inner states of its bottom path
    checked; its two ends are below the level for free (`square`,
    `square_short` for a bottom path of at most one edge).
  * `Column.lean`: a word below the pivot acts on the pivot column
    (`pcol_word`, `pivot_word_lt`); at a scale `k`, `IsCol v k u` (`2^k v`
    is the integer vector `u`), with the action of each generator on `u`
    (`isCol_neg`, `isCol_x`, `isCol_k`, `isCol_k_up`), `lde`, the odd entries,
    the first four odd entries and the syllable read off `u` (`lde_eq`,
    `oddS_eq`, `firstOdd_eq`, `syll_eq_pos`).
  * `SwapConj.lean`: conjugation by `X_[x,x+1]` renames any generator not
    involving both `x` and `x+1` ((2a)–(2c), (3a)–(3g); `conj_swap`).
  * `Checker.lean`, `Derive.lean`: rewriting chains on concrete indices
    checked by the kernel (`decide +kernel`), moved along order embeddings
    (`derivable_rename`, `emb4`, `emb6`, `emb8`).  The steps of `checkD` are
    relations of Table 1, read either way round (`rev_derivable`), and the
    derived relations (8a)–(8d), (9a)–(9g) of Propositions A.11, A.12 (and
    `K (−1)_[a] K ≈ X_[b,c] (−1)_[a] K (−1)_[a]`, from (4b)), each proved
    once at every choice of indices.  The chains are found by a search
    script (scratch): a BFS for short gaps, a normaliser for words of
    signed permutations, and a planner that moves a signed permutation
    through a `K` (`σ K_S τ ≈ σ' K_S' τ'`) by the passing relations and the
    renaming relations (3d)–(3g).
  * `CasePair.lean`: `rev_derivable` (a derivation read backwards: every
    generator is an involution), (8c) `ksym2`, signed permutations below
    the pivot keep a state below the level (`level_signed_lt`).
  * `PathSP.lean`: a closing path `X g Y` whose letters other than `g` are
    `(−1)`/`X` generators below the pivot stays below the level when its end
    does (`square_sp`, `square_sp0`; the states along `X` are signed
    permutations of the end), and `level_lt_of_col` (fewer odd entries at
    the scale of `s`).

  Proved cases: all of them.  Subcases 1.1 (`CaseZero.squareZ_X`), 1.2.1,
  1.2.2.1, 1.2.2.2 and 1.2.2.3 with `u_e` even (`CaseX.squareX_rename`: the syllable
  of `G s` is that of `s` renamed, and `G` closes the square), 1.2.3
  (`CasePair.squareX_pair'`), 1.2.2.3 with `u_e` odd (`CaseX8.squareX_odd'`,
  below), 2.1 (`CaseZero.squareZ_N`), 2.2
  (`CaseN.squareN_in`, `squareN_out`), 3.1 (`CaseZero.squareZ_K`;
  Subcases 3.1.1–3.1.4 raise the level, which the hypothesis excludes) and
  3.2.1 (`CaseK.squareK_disj`: `K` makes the even entries `0, …, 3` all odd,
  which raises the level, or all even, which keeps the syllable), and
  3.2.2–3.2.5 (`CaseKMeet.squareK_meet'`):
  * 3.2.2 and 3.2.4 (one or three of the first four odd entries among
    `0, …, 3`) raise the least denominator exponent (the four entries have
    an odd sum), so the hypothesis of the Main Lemma excludes them
    (`CaseK2.k_odd_raises`).
  * 3.2.5 (`CaseK4.squareK_four`): `K ≈ V K S` or `K S' K ≈ V K S` with `V`
    a signed permutation (Corollaries A.13, A.14); the 72 chains are in
    `Rel325`.
  * 3.2.3 (`CaseKMeet.two_ij`, `finish323`): `K s` has two odd entries
    `α < β` among `0, …, 3` (Lemma A.3), and the square closes by
    `X K_[0,1,2,c] Y` with `X`, `Y` signed permutations (Proposition A.15,
    which the paper proves for two of its twelve words).  Each of the 96
    relations (twelve configurations, eight sign patterns of a fixed
    parity each) reduces to the one instance of (5a) on `0, 1, 2, 3, c, d`
    (`Rel323`); the signs of `c, d` commute with `K_[0,1,2,3]` and are
    handled generically (`CaseK2.square_two`).

## Theorem 4.10 is complete

There is no `sorry`.  `#print axioms presentation` (and `presentationL`,
`complete`) gives `[propext, Classical.choice, Quot.sound]`.

The last case of Lemma A.20, Subcase 1.2.2.3 with `u_e` odd
(`CaseX8.squareX_odd'`): `G = X_[d,e]`, `e = d + 1` the fifth odd entry, `f, g, h`
the next three.  `s` and `r = G s` have the same odd entries, and at both the
first two syllables are on `a, b, c, d` and `e, f, g, h` (`eight_syll`).  The
square closes by `P = W⁻¹ K_[a,b,c,d] K_[e,f,g,h] X_[d,e] K_[e,f,g,h] K_[a,b,c,d] W`
followed by the syllable of `t`, with `W = (−1)_[a](−1)_[e]X_[a,e]` or
`(−1)_[a](−1)_[h]X_[a,h]`; the derivation is `W⁻¹ C W ≈ C` (`Rel1223`: (6a),
Proposition A.16) plus the signs of `d` and `e` exchanging across `X_[d,e]`
(`der1223`).  The case split is on the sum of the eight entries made
`≡ 1 (mod 4)`, `≡ 4` or `0 (mod 8)` (the paper's `ū ᵀ ū ≡ 0, 8 (mod 16)`); the
residue claims of Lemmas A.8–A.10 become two `omega` lemmas on that sum
(`par8_e`, `par8_h`), and the levels along both sides of the diagram follow
(`eight_lev_e`, `eight_lev_h`: the two `K`s after `W` keep the eight entries
even; the side of `q` is the same computation at `r`).

Every diagram and every intermediate level of Subcases 1.2.2.3, 3.2.3 and
3.2.5 was checked numerically first (exact rational arithmetic on random
states for `n = 6, …, 12`, scratch), as were the residue patterns of
Lemma A.3 and the sign parities.

## Errors found in the proof of Lemma A.20

* **Proposition A.16**: the printed proof derives the relation for
  `K_[e,f,g,h] K_[a,b,c,d] K_[a,b,c,e] K_[d,f,g,h]` in place of
  `C = K_[e,f,g,h] K_[a,b,c,d] X_[d,e] K_[a,b,c,d] K_[e,f,g,h]` (the two
  differ by `X_[d,e]` on the right), and uses (6a) in that form.  The
  statement holds; `Rel1223.rel1223_h` derives it as (6a) conjugated by
  `X_[e,h]`, which commutes with `C` by (8b).
* Subcases 3.2.2 and 3.2.4 state `level(r) = (j,k+1,1)`; `K` makes the four
  entries `0, …, 3` odd at scale `k+1`, so the last component counts those
  (the subcases raise the level either way).
* Proposition A.15 is proved for two of the twelve words; the others are
  "treated similarly".  All twelve, at every sign pattern that occurs,
  are derived here (`Rel323`), each checked numerically first.
