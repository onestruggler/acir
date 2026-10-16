# Errata

Matthew Amy, Neil J. Ross and Scott Wesley, [*A Sound and Complete
Equational Theory for 3-Qubit Toffoli-Hadamard
Circuits*](https://arxiv.org/abs/2407.11152v3), QPL 2024, EPTCS 406
(arXiv:2407.11152v3). Page numbers are those of the arXiv version.

These were found while formalising the paper in this directory. One relation
is missing from the presentation of Theorem 5.2, which makes that theorem false
as stated and leaves a gap in the proof of Theorem 6.3. Seven printed
equations are false, two of them in four places each. One paragraph
contradicts the paper's own formulas, one proof step is incomplete, and there
are a few small slips.

Every false equation below is refuted in [`Errata.agda`](Errata.agda) by one
entry at which its two sides differ, and every correction is checked there or
elsewhere in the development, as noted. [`gen/errata.py`](gen/errata.py)
repeats every check in exact rational arithmetic, and checks the schemas (63)
and (66) at every choice of indices.

**Conventions.** These are the paper's own (Section 2):

- M₀ = M ⊗ I ⊗ I, so qubit 0 is the most significant and |x₀x₁x₂⟩ is basis
  state 4x₀ + 2x₁ + x₂.
- CM_{j,k} applies M to qubit k when qubit j is |1⟩, and CCM_{j,k} applies M
  to the third qubit when qubits j and k are both |1⟩.
- Products, written · or ∘, are matrix products, so the rightmost factor acts
  first.
- Matrix entries are given as (row, column), counted from 0.

## 1. The relation r_K is missing from R₁ (Theorem 5.2)

Section 5.5 (p. 12) introduces the true relation

  (r_K)  K₁,₂ ≈ K_[4,5,6,7] · X₀ · K_[4,5,6,7] · X₀,

but R₁ = R₀ ∪ R₈₄ (Section 5.6, p. 12) consists of Figures 4 and 7 only, and
neither contains it. Figure 4 never mentions K_[0,1,2,3] or CCZ, and Figure 7
never mentions K₁,₂, so no relation of R₁ involves both K₁,₂ and
K_[0,1,2,3].

**r_K does not follow from R₁.** Here R₁ means Figures 4 and 7 with the
corrections of Section 2 below. Let J be the 8 × 8 all-ones matrix and
R = I − J/4. Then R² = I, and R commutes with every permutation matrix. Read
each gate of Figure 4 as R g R, and read K_[0,1,2,3] and CCZ as themselves:

- Every relation of Figure 4 holds, since it is conjugated by R.
- Every relation of Figure 7 holds unchanged. Its gates are K_[0,1,2,3], CCZ
  and circuits of permutation gates, and R commutes with those circuits.
- r_K fails: its left side has entry (0, 0) equal to −1/4, its right side
  1/2.

So ⟨Σ₁ | R₁⟩ is not O(8, 𝔻), and Theorem 5.2 is false as stated.

**Correction.** With r_K added, R₁⁺ = R₁ ∪ {r_K} presents O(8, 𝔻); this is
`theorem-5-2` in [`Theorems.agda`](Theorems.agda), and the countermodel is
`r_K-independent` ([`Independence.agda`](Independence.agda)). There r_K is
stated as K₁,₂ ≈ X₀ K_[0,1,2,3] X₀ K_[0,1,2,3]. That is the same relation,
because the printed right-hand side is K_[4,5,6,7] K_[0,1,2,3], this one is
K_[0,1,2,3] K_[4,5,6,7], and (96) equates the two.

**Effect on Theorem 6.3.** Its proof (p. 14) uses Theorem 5.2 ("O(8, 𝔻) ≅
⟨Σ₁, R₁⟩ with R₁ ⊆ R₂"). With r_K added, R₂⁺ = R₂ ∪ {r_K} presents TofH(3):
this is `theorem-6-3`. We do not know whether r_K follows from R₂, that is,
whether Figure 8 makes up for the missing relation. The countermodel above
does not extend to H₂ directly: the only 8 × 8 matrix that satisfies
(102)–(107) with H₂ read as it is 0, which fails (108).

**Counts.** The presentations have 66 and 73 relations, not the 65 of the
Introduction (p. 1) and the Conclusion (p. 14).

## 2. False equations

| Where | Printed | Correct | Entry: printed sides | In `Errata.agda` |
| --- | --- | --- | --- | --- |
| (33), Fig. 4, p. 8 | CCX₀,₁ ≈ σ₁,₂ · CCX₀,₂ · σ₀,₂ | CCX₀,₁ ≈ σ₁,₂ · CCX₀,₂ · σ₁,₂ | (1, 1): 1 vs 0 | `r033-false` |
| §5.5, p. 11 | CCX₁,₂ = X_[6,7] | CCX₀,₁ = X_[6,7] | (3, 3): 0 vs 1 | `x67-false` |
| (r_CX), §5.5, p. 11 | CX₀,₁ ≈ X_[2,6] · X_[3,7] | CX₀,₁ ≈ X_[4,6] · X_[5,7] | (2, 2): 1 vs 0 | `rCX-false` |
| §5.6, p. 12 | (−1)_[0] = X₀ X₁ CCZ X₁ X₀ | (−1)_[0] = X₀ X₁ X₂ CCZ X₂ X₁ X₀ | (0, 0): −1 vs 1 | `m0-false` |
| (97), Fig. 7, p. 12 | X_[0,1] K ≈ K X_[0,1] (−1)_[1] (−1)_[3] | X_[0,1] K ≈ K X_[1,3] (−1)_[1] (−1)_[3] | (1, 1): 1/2 vs −1/2 | `r097-false` |
| (100), Fig. 7, p. 12 | K K_[1,3,4,5] ≈ K_[1,3,4,5] K | K K_[1,3,4,5] ≈ K_[2,3,4,5] K_[0,1,2,4] | (0, 3): 0 vs 1/2 | `r100-false` |
| §5.7, p. 13 | CCZ = K₁,₂∘CZ₁,₂∘X₀∘K∘X₀∘CZ₁,₂∘K∘X_[5,6] | CCZ = K₁,₂∘CZ₁,₂∘X₀∘K∘X₀∘CZ₁,₂∘K₁,₂∘X_[5,6] | (4, 4): 1 vs 1/2 | `ccz-false` |

In the table, K is K_[0,1,2,3]. Notes on each row:

- **(33).** As printed, R₀ is unsound. The correction is relation `r33` of
  [`Syntactics.agda`](Syntactics.agda), checked by
  [`Soundness.agda`](Soundness.agda).
- **CCX₁,₂ = X_[6,7].** The paper uses this to replace X_[6,7] in R₈³ by
  CCX₁,₂. In fact CCX₁,₂ = X_[3,7] (`ccx12`), and X_[6,7] is CCX₀,₁, as the
  paper itself says on p. 9. So X_[6,7] in Figure 7, in (90) and (93), must
  be read as CCX₀,₁. Section 5.6 lists circuits only up to X_[5,6]. CCX₀,₁ =
  X_[6,7] is `StdMatrices.mT6`.
- **r_CX.** X_[2,6] X_[3,7] is CX₁,₀ (`cx10`), and the correction is `rCX`.
  r_CX is a step of the Tietze sequence only and does not reach Figure 7.
- **The alias (−1)_[0].** The printed word is (−1)_[1] (`m1`). The corrected
  alias is `m0` in `Syntactics.agda`, checked by `StdMatrices.mm0`.
- **(97).** The correction is Li, Ross and Selinger's (4a). The same misprint
  is in (78) (Fig. 6, p. 11) and (125) (Fig. 10, p. 41), which are (97) on
  the two-level generators, and in the schema (63) (Fig. 5, p. 9). There the
  correct right-hand side is K_[a,b,c,d] X_[b,d] (−1)_[b] (−1)_[d]. As
  printed, (63) fails at all 70 choices of a < b < c < d < 8, and the
  corrected schema holds at all of them (`gen/errata.py`). The correction is
  relation `r97`, checked by `Soundness.agda`.
- **(100).** The correction is Li, Ross and Selinger's (5a). The same misprint
  is in (81) (Fig. 6) and (128) (Fig. 10), and in the schema (66) (Fig. 5).
  The correct schema is K_[a,b,c,d] K_[b,d,e,f] ≈ K_[c,d,e,f] K_[a,b,c,e]. As
  printed, (66) fails at all 28 choices of six indices, and the corrected
  schema holds at all of them. The correction is relation `r100`.
- **The CCZ decomposition.** It is false in either reading of ∘. The
  correction replaces the second K_[0,1,2,3] by K₁,₂ (`ccz`); by r_K, that
  factor is K_[0,1,2,3] K_[4,5,6,7]. The other decomposition, K_[0,1,2,3] =
  (K₁,₂ ∘ CCZ)³ ∘ X_[5,6], is right as printed (`nk`). Neither presentation
  uses these decompositions.

## 3. The control states of K_[0,1,2,3] (Section 5.5, pp. 11–12)

The paper says that K_[0,1,2,3] is a K₁,₂ gate applied when qubit 0 is in state
|1⟩, and X₀ ∘ K_[0,1,2,3] ∘ X₀ one applied when qubit 0 is in state |0⟩. It
is the other way round: K_[0,1,2,3] acts on states 0–3, where qubit 0 is |0⟩.
The paper says so itself at the end of Section 5.6, where K_[0,1,2,3] is "a
negatively controlled K gate", and on p. 9, where K_[4,5,6,7], which is
X₀ K_[0,1,2,3] X₀, is "a controlled K-gate". The relation r_K itself is right.

## 4. A gap in the proof of Lemma 6.1 (pp. 13–14)

The inductive step moves H₂ past the first letter x of w "by one of Relations
(102), (103), (104), (105), (106) and (107)". Those relations cover only six
letters of Σ₁: X₀, CX₀,₁, CCX₁,₂, CCZ, K₁,₂ and K_[0,1,2,3]. Σ₁ has 25
letters. For the other 19 (X₁, Z₀, CZ₀,₁, σ₀,₁, …), x must first be rewritten
by its defining relation, (1)–(19) of Figure 4. These define each derived gate
of Σ_D in terms of earlier ones, and H₂ is then moved past the result letter by
letter: an induction on the order of the definitions. The lemma is true:
[`Push.agda`](Push.agda) proves it this way.

## 5. Small slips

- **p. 3, the definition of CCM_{j,k}:** l ∈ {1, 2, 3} \ {j, k} should be
  l ∈ {0, 1, 2} \ {j, k}.
- **p. 13, Section 5.7:** "the set Σ_D ∪ {CCZ} is minimal, whereas the set
  Σ_D ∪ {K_[0,1,2,3]} is not". Σ_D itself is not minimal, since it contains
  the 19 derived gates. Presumably Σ₀ is meant: Σ₀ ∪ {CCZ} is Σ_Z of Theorem
  5.3, and in Σ₀ ∪ {K_[0,1,2,3]} the gate K₁,₂ is redundant, by r_K.
- **p. 14, proof of Lemma 6.1:** in "Then H₂ · u ∼_{R₂} u′ · w′ · H₂ by the
  transitivity of (∼_{R₂})", H₂ · u should be H₂ · w.
- **p. 31, Appendix C:** "CX₁,₂ is a reflection about the normal vector
  |−⟩ ⊗ |1⟩ ⊗ |1⟩". That reflection is CCX₁,₂. CX₁,₂ is not a reflection:
  its −1-eigenspace has dimension 2.
- **p. 41, Figure 10:** ρ ends in an extra X_[0,4] that it does not have in
  Figures 5–7. This is harmless, because (129) holds with either ρ.

## Checking

`Errata.agda` typechecks in about half a minute given the interfaces of this
directory (Agda 2.8.0, standard-library 2.4, `--safe --without-K`).
`gen/errata.py` needs only Python 3:

```sh
cd gen && python3 errata.py
```

An independent formalisation of the same paper in
[`../CCX+HH-3qubit/`](../CCX+HH-3qubit/ERRATA.md) records the same
corrections for Sections 1–3, except r_CX and the CCZ decomposition. Those
two, and Sections 4 and 5, are new here.
