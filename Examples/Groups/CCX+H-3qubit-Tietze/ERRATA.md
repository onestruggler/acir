# Errata for the three qubit Toffoli Hadamard presentation

These corrections concern Matthew Amy, Neil J. Ross and Scott Wesley,
*A Sound and Complete Equational Theory for 3-Qubit Toffoli-Hadamard
Circuits*, [arXiv:2407.11152v3, 12 August 2024](https://arxiv.org/abs/2407.11152v3),
EPTCS 406, pp. 1–43. They were identified while formalising the circuit
presentations in this repository.

The printed formulas below contain five matrix errors, one reversal of
control states, and an omitted defining relation. The omitted relation
is independent of the corrected dyadic rules and must be retained in
the repaired dyadic presentation.

## Conventions

Use the computational basis ordered as
`|000⟩, |001⟩, …, |111⟩`, with qubit 0 the most significant bit.
Products are matrix products: the rightmost factor acts first.
The subscripts of `CCX` name its two controls. Write

$$
N=K_{[0,1,2,3]},\qquad P=K_{[4,5,6,7]}=X_0 N X_0,
\qquad M_j=(-1)_{[j]}.
$$

Thus `N` applies `H ⊗ H` to qubits 1 and 2 when qubit 0 is **0**;
`P` does so when qubit 0 is **1**. Equality includes global scalars.
Matrix-entry witnesses use zero-based row and column indices.

## Corrections to formulas and control states

### Equation 33 in Figure 4

On page 8, the final swap in (33) is printed as `σ₀,₂`. It must be
`σ₁,₂`:

$$
\mathrm{CCX}_{0,1}\approx
\sigma_{1,2}\,\mathrm{CCX}_{0,2}\,\sigma_{1,2}.
$$

The supplied TIETZE relation file already uses the corrected swap:
[`dyadic.rels`](tools/dyadic.rels), `symmetry_CCX_b`.

### The exchange of states 6 and 7 in Section 5.5

On page 11, replace `CCX₁,₂ = X_[6,7]` with

$$
\mathrm{CCX}_{0,1}=X_{[6,7]}.
$$

With the paper's control convention, `CCX₁,₂` exchanges states 3 and 7.

### The control states in Section 5.5

The explanation spanning pages 11–12 reverses the control states of
`K_[0,1,2,3]` and `X₀ K_[0,1,2,3] X₀`. Their controls are on **0**
and **1**, respectively, as specified in the conventions above.
The displayed relation `r_K` itself is a true matrix identity.

### The sign alias in Section 5.6

On page 12, the alias for `(-1)_[0]` omits `X₂` on both sides of `CCZ`.
Replace it with

$$
M_0=X_0 X_1 X_2\,\mathrm{CCZ}\,X_2 X_1 X_0.
$$

The printed expression `X₀ X₁ CCZ X₁ X₀` changes the sign of state 1,
rather than state 0.

### Equations 63, 78, 97 and 125

In (97), the exchange on the right must be `X_[1,3]`, giving

$$
X_{[0,1]}N\approx N X_{[1,3]}M_1M_3.
$$

The same correction applies to (78) in Figure 6 and (125) in Figure 10.
In the general schema (63) in Figure 5, replace the right-hand
`X_[a,b]` with `X_[b,d]`:

$$
X_{[a,b]}K_{[a,b,c,d]}
\approx K_{[a,b,c,d]}X_{[b,d]}M_bM_d
\qquad(a<b<c<d).
$$

### Equations 66, 81, 100 and 128

The commutation printed in (100) is false. Replace it with

$$
K_{[0,1,2,3]}K_{[1,3,4,5]}
\approx K_{[2,3,4,5]}K_{[0,1,2,4]}.
$$

The same correction applies to (81) in Figure 6 and (128) in Figure 10.
The general schema (66) in Figure 5 becomes

$$
K_{[a,b,c,d]}K_{[b,d,e,f]}
\approx K_{[c,d,e,f]}K_{[a,b,c,e]}
\qquad(a<b<c<d<e<f).
$$

## Retain the defining relation for K

Section 5.5 introduces `r_K` while adding the circuit generators.
Section 5.6 then defines `R₁` using only Figures 4 and 7, which omit
this relation. In terms of the negatively controlled gate `N`, retain

$$
(r_K)\qquad K_{1,2}\approx N X_0 N X_0.
$$

The paper's spelling `K₁,₂ ≈ P X₀ P X₀` is equivalent: its right side
is `PN`, the right side above is `NP`, and (96) equates these products.

### Independence from the corrected dyadic rules

Let `J` be the 8 by 8 all-ones matrix and set

$$
R=I-\tfrac14J.
$$

Then `R² = I`, and `R` commutes with every permutation matrix.
Interpret each Toffoli-K generator `g` as `RgR`, while keeping `CCZ`
and `N` at their intended matrices. All corrected Figure 4 relations
hold by conjugation. Each exchange abbreviation remains its intended
permutation, so all corrected Figure 7 relations also hold.

However, the two sides of `r_K` have different entries at `(0,0)`:

$$
(R K_{1,2}R)_{0,0}=-\tfrac14,
\qquad
(N X_0 N X_0)_{0,0}=\tfrac12.
$$

Consequently, `r_K` is not derivable from the 65 corrected dyadic
relations. The Agda certificate uses the reduction of this model
over `ℤ/17ℤ`, where these entries are 4 and 9.

### Effect on the completeness statements

Let `R₁ᶜ` denote the 65 equations of Figures 4 and 7 with the formula
and alias corrections above. Let `R₂ᶜ` add the seven Figure 8 equations.
The presentations verified in this repository use

$$
R_1^+=R_1^{\mathrm c}\cup\{r_K\},\qquad
R_2^+=R_2^{\mathrm c}\cup\{r_K\}.
$$

- The repaired dyadic presentation uses `R₁⁺` and presents
  `O(8, ℤ[1/2])`. It retains 66 equations in this transcription.
- The repaired Toffoli-Hadamard presentation uses `R₂⁺` and presents
  `TofH(3)`: orthogonal matrices of the form `A/(√2)ᵏ` with integer
  `A` and natural `k`. It retains 73 equations.

The countermodel proves incompleteness of `R₁ᶜ` for the intended gate
semantics. It does **not** establish independence after the seven
Hadamard relations are added. Whether `r_K` follows from `R₂ᶜ`, and
hence whether those 72 corrected equations alone are complete, remains
unresolved in this development.

## Matrix witnesses and formal certificates

For each false printed equality, one entry of its two matrices differs:

| Printed equality | Entry | Left side | Right side | Theorem in [Errata.agda](Errata.agda) |
| --- | --- | --- | --- | --- |
| (33) | `(1,1)` | `1` | `0` | `r033-false` |
| Section 5.5 exchange alias | `(3,3)` | `1` | `0` | `t67-alias-false` |
| Section 5.6 sign alias | `(0,0)` | `-1` | `1` | `m0-alias-false` |
| (97) | `(1,0)` | `1/2` | `-1/2` | `r097-false` |
| (100) | `(0,3)` | `0` | `1/2` | `r100-false` |

The corrected circuit equations are recorded in
[Syntactics.agda](Syntactics.agda) and verified by
[Soundness.agda](Soundness.agda).
The general corrections to (63) and (66) are `r4a` and `r5a` in
[CCX+HH-TwoLevel/Syntactics.agda](../CCX+HH-TwoLevel/Syntactics.agda),
with soundness proved in
[CCX+HH-TwoLevel/Soundness.agda](../CCX+HH-TwoLevel/Soundness.agda).
[MissingK.agda](MissingK.agda) proves `K-definition-underivable` for
the dyadic rule selection. [Repaired/KMatrix.agda](Repaired/KMatrix.agda)
and [Repaired/Soundness.agda](Repaired/Soundness.agda) check the retained
definition in the intended semantics.

The full repaired presentation is
[Repaired/Presentation.agda](Repaired/Presentation.agda), with public
exports in [Theorems.agda](Theorems.agda). The separate development
[CCX+HH-3qubit-opus/Theorems.agda](../CCX+HH-3qubit-opus/Theorems.agda)
also states both repaired group presentations and dyadic independence.
The formal certificates were checked with Agda 2.8.0 and
standard-library 2.4, using `--safe` and `--without-K`.
