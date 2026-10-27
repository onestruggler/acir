/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-Π, §4.2: Theorems 4.13 and 4.14

Fang, Heunen and Kaarsgaard (POPL 2026, arXiv:2506.06835): the generators
`𝒢ₙ` of Definition 4.5 and the relations of Figure 6 present the group
`Oₙ(ℤ[1/√2])` of orthogonal `n × n` matrices with entries in `ℤ[1/√2]`,
for every `n` (Theorem 4.13, soundness; Theorem 4.14, completeness; with
Theorem 4.8, generation, the words reach every element of the group).
Indices start at 0 (the paper's at 1).
-/
import QCert.HadamardPi.Soundness

namespace QCert.HadamardPi

/-- Theorem 4.13 (Soundness of `≈`): derivably equal words have the same
matrix. -/
theorem theorem_4_13 {n : ℕ} {w w' : Word (Gen n)} (h : Derivable Fig6 w w') :
    FreeMonoid.lift (sem n) w = FreeMonoid.lift (sem n) w' :=
  derivable_sound fig6_sound h

/-- Theorem 4.14 (Completeness of `≈`), with soundness (Theorem 4.13) and
generation (Theorem 4.8): the generators `𝒢ₙ` and the relations of
Figure 6 present `Oₙ(ℤ[1/√2])`. -/
theorem theorem_4_14 (n : ℕ) : IsPresentationOf (Fig6 (n := n)) (sem n) where
  grouplike := fig6_grouplike
  sound := fig6_sound
  complete := sorry
  surjective := sorry

end QCert.HadamardPi
