/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément (2019): Theorem 4.1

The generators `(-1)[j]`, `H[j,k]`, `X[j,k]` (`j ≠ k`) and the relations
(1)–(21), with (22) when `n = 2`, present `Uₙ(ℤ[1/√2]) = Oₙ(ℤ[1/√2])`
for every `n`: soundness (Section 3.5), completeness (Theorem 4.1) and
generation (Lemma 1.4, by the real Giles–Selinger algorithm, Algorithm 1).
-/
import QCert.Clement2019.Soundness

namespace QCert.Clement2019

/-- Theorem 4.1 (completeness), with soundness (Section 3.5) and generation
(Lemma 1.4): the relations (1)–(22) present `Oₙ(ℤ[1/√2])`. -/
theorem theorem_4_1 (n : ℕ) : IsPresentationOf (Rel (n := n)) (sem n) where
  grouplike := rel_grouplike
  sound := rel_sound
  complete := sorry
  surjective := sorry

end QCert.Clement2019
