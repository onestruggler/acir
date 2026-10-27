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

## Remaining `sorry`

* `Theorem.complete` — **Theorem 4.10 (completeness)**, i.e. the Main
  Lemma 4.7 with its case analysis (Appendix A: Lemmas A.19, A.20, A.21 and
  the derived relations, Propositions A.11–A.16).  Everything else,
  including `presentationL`, is proved from it.
