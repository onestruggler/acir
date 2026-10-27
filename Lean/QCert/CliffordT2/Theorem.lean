/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Generators and relations for two-qubit Clifford+T operators

Bian and Selinger (QPL 2022, arXiv:2204.02217), Theorem 2.1: the
two-qubit Clifford+T group is presented by the generators
`𝒳 = {ω, H₀, H₁, S₀, S₁, T₀, T₁, CZ}` (`Syntax.Gen`) and the relations
(C1)–(C20) of Figure 1 (`Syntax.Rel`), with the generators read as the
4 × 4 matrices of Section 2 (`Semantics.sem`).

As a `QCert` statement: the relations are a sub-presentation of the
unitary group `U(4)` (they present the subgroup the generators generate,
the two-qubit Clifford+T group), and equally of `U₄(ℤ[1/√2, i])`, the
group of Greylyn's Theorem 4.1 that contains it.
-/
import QCert.CliffordT2.Soundness
import QCert.CliffordT2.Completeness

namespace QCert.CliffordT2

open Matrix

/-- **Theorem 2.1**: Figure 1 presents the subgroup of `U(4)` generated
by `ω, H₀, H₁, S₀, S₁, T₀, T₁, CZ`. -/
theorem theorem_2_1 : IsSubPresentationOf Rel sem :=
  ⟨grouplike, sound, complete⟩

/-- **Theorem 2.1**, as a sub-presentation of `U₄(ℤ[1/√2, i])`. -/
theorem theorem_2_1_U : IsSubPresentationOf Rel semU :=
  (isSubPresentationOf_iff_of_injective (U_ZInvSqrt2I 4).subtype Subtype.val_injective
    (fun _ => rfl)).2 theorem_2_1

end QCert.CliffordT2
