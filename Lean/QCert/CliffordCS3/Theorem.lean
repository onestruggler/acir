/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Generators and relations for three-qubit Clifford+CS operators

Bian and Selinger (QPL 2023, arXiv:2306.08530), Theorem 3.1: the
three-qubit Clifford+CS group is presented by the generators
`𝒳 = {i, K₀, K₁, K₂, S₀, S₁, S₂, CS₀₁, CS₁₂}` (`Syntax.Gen`) and the
relations of Figure 2 (`Syntax.Rel`), with the generators read as the
8 × 8 matrices of Section 2.1 (`Semantics.sem`).

As a `QCert` statement: the relations are a sub-presentation of the
unitary group `U(8)` (they present the subgroup the generators generate,
the three-qubit Clifford+CS group), and equally of `U₈(ℤ[1/2, i])`, the
group of the authors' Theorem 2.1 that contains it.
-/
import QCert.CliffordCS3.Soundness
import QCert.CliffordCS3.Completeness

namespace QCert.CliffordCS3

open Matrix

/-- **Theorem 3.1**: Figure 2 presents the subgroup of `U(8)` generated
by `i, K₀, K₁, K₂, S₀, S₁, S₂, CS₀₁, CS₁₂`. -/
theorem theorem_3_1 : IsSubPresentationOf Rel sem :=
  ⟨grouplike, sound, complete⟩

/-- **Theorem 3.1**, as a sub-presentation of `U₈(ℤ[1/2, i])`. -/
theorem theorem_3_1_U : IsSubPresentationOf Rel semU :=
  (isSubPresentationOf_iff_of_injective (U_ZHalfI 8).subtype Subtype.val_injective
    (fun _ => rfl)).2 theorem_3_1

end QCert.CliffordCS3
