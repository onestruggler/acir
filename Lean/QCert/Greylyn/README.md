# Greylyn: generators and relations for U₄(ℤ[1/√2, i])

S. E. M. Greylyn, *Generators and relations for the group U₄(ℤ[1/√2, i])*,
M.Sc. thesis, Dalhousie University, 2014, arXiv:1408.6204.

## Main theorem

```lean
theorem QCert.Greylyn.presentation (n : ℕ) (hn : n ≤ 4) : IsPresentationOf (Rel n) (sem n)
```

(`Theorem.lean`) is the thesis' Theorem 22, with Theorem 7 (generation),
for every `n ≤ 4`: the one- and two-level matrices `X_[α,β]`, `H_[α,β]`
(`α < β`) and `ω_[α]` (`Gen n`, the generating set `(*)` of Definition 6)
with the equations (1)–(20) of Table 3.1 (`Rel n`) present the group
`U_ZInvSqrt2I n` of unitary `n × n` matrices over `ℤ[1/√2, i]`.  The thesis
states the theorem for `n = 4`; its proof is for states of dimension at
most `4`, the one place this is used being Subcase 4.3.3 of the Main Lemma
(Lemma 39).

**There is no `sorry`.**  `#print axioms QCert.Greylyn.presentation` gives
`propext, Classical.choice, Quot.sound`.  No `native_decide`, `axiom` or
`implemented_by` is used; computations are `decide` or `decide +kernel`.

## Conventions

* Indices are `Fin n`, from `0`; the thesis numbers them from `1`.  So the
  basic generators of Definition 28, `H_[1,2]`, `ω_[1]`, `X_[α,α+1]`, are
  `H_[0,1]`, `ω_[0]`, `X_[a,a+1]` here.
* A word `w` denotes the product of its letters' matrices in the written
  order (`FreeMonoid.lift (sem n)`, written `⟪w⟫` locally); a state `s` is
  an element of `U_ZInvSqrt2I n` and `⟪w⟫ * s` is the thesis' `w s`.
* `ℤ[ω]` is `ZOmega`, quadruples `a + bω + cω² + dω³` with `ω⁴ = -1`;
  `δ = 1 + ω`.  `HasNum v k w` says `δᵏ v = w` with `w` over `ℤ[ω]` (the
  numerator of `v` at the δ-exponent `k`), and `lde v` is the least such `k`
  (Definition 9).
* The level of a state (Definition 19) is `(p + 1, k, m)` for the `0`-based
  pivot `p`, as a lexicographic triple (`level`); `prof` is its last two
  components.
* Derivations from Table 3.1 are equalities in the presented monoid
  `Pres n` (`cl w = cl v ↔ w ≈ v`).

## Correspondence with the thesis

| Thesis | File |
| --- | --- |
| §2.4: `ℤ[ω]`, Example 8, Definition 10, Lemmas 11, 12, the units of Lemma 14 | `ZOmega.lean` |
| Definition 9 (δ-exponents), Lemma 14, the parity count in the proof of Lemma 13 | `Exponent.lean` |
| Definition 6 (the generators), Table 3.1 (equations (1)–(20)) | `Syntax.lean` |
| Definitions 3, 4 (one- and two-level matrices) | `Semantics.lean` |
| Lemma 23 (soundness), invertibility of the generators | `Soundness.lean` |
| Algorithm 16 (pivot columns), Definition 19 (levels) | `Algorithm.lean` |
| Definition 17 (syllables), step 2 of Algorithm 16, Lemma 12 on numerators | `Syllable.lean` |
| Theorem 18 (termination), the normal words of Definition 25 | `Normal.lean` |
| §3.3.5: Lemma 32 for one edge (`Step`), Convention 1, Definition 28, Lemma 33 | `Induction.lean` |
| derivations modulo Table 3.1 (`e1` … `e20`) | `Pres.lean` |
| Lemma 24: Table 3.2, equations (21)–(32) | `Derived.lean` |
| Lemma 30 (a), (b): generators as words of basic generators | `Decomp.lean` |
| Lemma 30 (c): the levels along those words | `LevelBound.lean` |
| proof of Lemma 32, base case (the edges out of `I`) | `BaseCase.lean` |
| residues modulo `δ²`, `δ³` for the Main Lemma | `Residue.lean` |
| Lemma 31: the conclusion (`Square`), retrograde edges (Definition 40), levels along paths | `Square.lean` |
| Lemma 31, Case 1 (`H_[1,2]`) | `MainH.lean` |
| Lemma 31, Case 2 (`ω_[1]`) | `MainOmega.lean` |
| Lemma 31, Cases 3–5 (`X_[α,α+1]`) but Subcases 4.3, 4.4 | `MainX.lean` |
| §3.3.6: Lemmas 35–39 | `Technical.lean` |
| Lemma 31, Subcases 4.3 (4.3.1–4.3.3) and 4.4 | `MainHard.lean` |
| Lemma 31, Lemma 32, Theorem 34 (completeness) | `Completeness.lean` |
| Theorem 22 | `Theorem.lean` |

The induction of §3.3.5 (normal words that reduce every state to `I`, and
`Step` along every edge, give a presentation) is the shared module
`QCert/Synthesis.lean`, which the Bian–Selinger development uses too.

## Formalization choices

* **Squares.**  A square of the Main Lemma at `s` with basic generator `x`
  (`Square s x`) is a state `q`, normal edges `x s ⇒ q` labelled `N'`, a
  path `G'` from `t = N s` (`N` the syllable of `s`) all of whose states
  have level below `level s` (`AllBelow`), and `N' x ≈ G' N`.  Paths of `X`
  and `ω` letters keep the profile of the pivot column (`allBelow_B`);
  paths with `H` letters are checked state by state.
* **Cases 3–5.**  `MainX.lean` treats `X_[a,a+1]` for every `a` at once,
  configuration by configuration of the first two odd entries `α < β` of
  the pivot column against `a, a + 1`; the thesis details `X_[1,2]` and
  `X_[2,3]` and calls the rest analogous.
* **Subcases 4.3 and 4.4.**  `square_X_hard` first shows that the
  configuration (first two odd entries `α < a`, entry `a + 1` odd) forces
  `n = 4`, `α = 0`, `a = 1`, pivot `3` and all four entries odd, by the
  parity count of Lemma 13.  The square is then assembled from its faces
  (`hard_alg`) with the path `G₀` of (31) or (32) between diagonal phase
  words, and the levels along `G₀` are checked from both ends
  (`allBelow_path`: the last three states are those along
  `H_[k,l] H_[i,j] H_[2,3]` from the end of the path, each `H` being an
  involution).
* **Lemma 38.**  The thesis cites Ross–Selinger for it; it is proved here
  directly (`lde_ne_one`).
* **Lemma 30 (c)** (the levels of the basic edges replacing a simple edge)
  is proved in `LevelBound.lean`.

## Errors in the thesis

Numbers are those printed in the PDF.  None of these errors affects the
truth of Theorem 22; each was worked around as described.

1. **Definition 19.**  "`(j,k,m) < (j',k',m')` if `j' < j`" has the
   inequality backwards; the order is lexicographic, as the text says and
   Theorem 18 needs (`j < j'`).
2. **Algorithm 16, step 2(b).**  "`u_ℓ ≡ ω^q (mod δ^q)`" should be
   `(mod δ³)`.
3. **Lemma 15.**  "`G_q G_{n−1} ⋯ G_1 v`" should be `G_q G_{q−1} ⋯ G_1 v`.
4. **Proof of Lemma 30.**  "`⟦G⟧ e_α ≠ α`" should be `≠ e_α`.
5. **Proof of Lemma 12** (harmless gap).  Once `j = m − ℓ` is reduced
   modulo `4`, `ω^j ω^ℓ` is `±ω^m`, not `ω^m`; the claim survives because
   `δ³` divides `2`, so `−1 ≡ 1 (mod δ³)`.
6. **Subcase 1.7.2.**  The pivot column of `r` is computed as
   `(√2 ω^ι, √2 ω^ι, 0, …)`; it is `(ω^ι/√2, ω^ι/√2, 0, …)`, which is what
   the rest of the argument uses.
7. **Subcase 2.1, `z = 0`.**  The thesis uses
   `H_[1,α] ω⁴_[1] ≈ X_[1,α] H_[1,α]` and `G' = X_[1,α]`.  That equation is
   false: on the indices `1, α`, `H · diag(−1, 1) = (1/√2)[[−1, 1], [−1, −1]]`
   while `X · H = (1/√2)[[1, −1], [1, 1]]`, its negative.  What holds is
   `H_[j,k] ω⁴_[j] ≈ ω⁴_[j] ω⁴_[k] X_[j,k] H_[j,k]` (`Derived.eH4`), and the
   square closes with `G' = ω⁴_[1] ω⁴_[α] X_[1,α]` (`MainOmega.lean`).
8. **Subcase 4.1.**  "Thus `level(r) = (j + 1, 0, 0)`" (with `j ≤ 2`): the
   pivot of `r = X_[2,3] s` is column `3`, so `level(r) = (3, 0, 0)`; and the
   displayed matrix of `r` exchanges rows `3, 4` of `s` instead of rows
   `2, 3`.  The argument (the edge is retrograde) is unaffected.
9. **Case 4, after Subcase 4.2.**  "Almost all other cases are directly
   analogous to Case 2" should refer to Case 3 (the cases of `X_[1,2]`).
   Moreover not every configuration of `X_[α,α+1]` has a counterpart for
   `X_[1,2]`: with `k = 0`, pivot `α + 1` and pivot column `ω^m e_c`,
   `c < α`, the square closes with `G' = X_[c,α]` by (12) and (13)
   (`MainX.lean`), a configuration `X_[1,2]` does not have.
10. **Subcase 4.3.1, 4.3.2: an unchecked state.**  The thesis checks the
    levels of `t, t', q, q', t'', q''` along
    `G' = H_[3,4] H_[2,4] H_[1,3] X_[2,3] H_[2,4] H_[1,3] H_[3,4]`, but not
    the two states between the `H`'s of `H_[2,4] H_[1,3]` (`H_[1,3] t'` and
    `H_[1,3] q'`; likewise `H_[2,3] t'`, `H_[2,3] q'` in Subcase 4.3.2).
    They are below `s` too: their pivot columns have δ-exponent `k − 1`,
    because `δ²` divides the sum and the difference of the two entries the
    first `H` combines, by the case hypothesis on `a + b + c + d` (checked
    here, `vside`).
11. **Subcase 4.4: the phases do not match.**  The thesis reduces to
    Subcase 4.3 with the phase words `ω^{−h}_[1] ω^{−h}_[2] ω^{−ℓ}_[3] ω^{−τ}_[4]`
    after `N = H_[1,2] ω^m_[1]` and `ω^{−ℓ}_[1] ω^{−ℓ}_[2] ω^{−h}_[3] ω^{−τ}_[4]`
    after `N' = H_[1,2] ω^φ_[1]` (with the typo `ω^{−h}_[1] ω^{−τ}_[1]` for
    `ω^{−h}_[3] ω^{−τ}_[4]` in the first display, and `1/δ⁴` for `1/δᵏ` in
    `v_r`).  Then `t` and `q` are as in Subcase 4.3 only up to the phase on
    the first entry: `m − h` and `φ − ℓ` agree modulo `4` but not always
    modulo `8`.  For instance with residues `(ι, h, ℓ) = (1, 0, 3)`,
    `m = 3`, `φ = 2`, the phases on the first entry are `ω³` and `ω⁷`, and
    the square does not commute.  An exact simulation over `ℚ(ω)`
    (322 random states of `U₄(ℤ[1/√2, i])` with all four pivot entries odd)
    finds the thesis' square failing for 17 of the 56 residue triples
    `(ι, h, ℓ)` that occur.  Here the phases are
    `E = ω^{e}_[0] ω^{e}_[1] ω^{f}_[2] ω^{g}_[3]` with `e ≡ −h`, `g ≡ −τ`
    (mod 4) and `f ≡ e + m − φ (mod 8)`, and `E_r` is `E` with the indices
    `1, 2` exchanged; then `f + φ ≡ e + m (mod 8)` and the square
    `N' X_[1,2] ≈ E_r⁻¹ G₀ E N` holds exactly (`hard_alg`, checked on all
    322 states before it was proved).

## Building

```
wsl --exec bash -lc 'cd /mnt/d/work2/acir/Lean && ./check.sh QCert/Greylyn/Theorem.lean'
```
