/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément (2019): Theorem 4.1

The generators `(-1)[j]`, `H[j,k]`, `X[j,k]` (`j ≠ k`) and the relations
(1)–(21), with (22) when `n = 2`, present `Uₙ(ℤ[1/√2]) = Oₙ(ℤ[1/√2])`
for every `n`: soundness (Section 3.5), completeness (Theorem 4.1) and
generation (Lemma 1.4, by the real Giles–Selinger algorithm, Algorithm 1).

Completeness is not Clément's proof (his Main Lemma 4.4, Section 5): it is
Hadamard-Π's Theorem 4.14 carried over by the syntactic equivalence of the
two theories (`Equivalence.lean`): two Clément words with the same matrix
have writings over `𝒢ₙ` with the same matrix (`lift_tr`), which are equal by
Figure 6, hence the words are equal by Clément's relations
(`clement_iff_fig6`).
-/
import QCert.Clement2019.Equivalence
import QCert.HadamardPi.Theorem

namespace QCert.Clement2019

open QCert.HadamardPi

/-- Lemma 1.4 (generation): every element of `Oₙ(ℤ[1/√2])` is a product of
generators.  Clément's Algorithm 1 outputs single generators where
Hadamard-Π's outputs syllables of the same generators, so we use the
latter (`QCert.HadamardPi.lift_sem_surjective`). -/
theorem lemma_1_4 (n : ℕ) : Function.Surjective (FreeMonoid.lift (sem n)) := by
  intro M
  obtain ⟨w, hw⟩ := HadamardPi.lift_sem_surjective M
  exact ⟨FreeMonoid.map ofFig6 w, by rw [lift_ofFig6, hw]⟩

/-- Theorem 4.1 (completeness), with soundness (Section 3.5) and generation
(Lemma 1.4): the relations (1)–(22) present `Oₙ(ℤ[1/√2])`.  Completeness
comes from Hadamard-Π's Theorem 4.14 through `clement_iff_fig6`. -/
theorem theorem_4_1 (n : ℕ) : IsPresentationOf (Rel (n := n)) (sem n) where
  grouplike := rel_grouplike
  sound := rel_sound
  complete := fun w w' h =>
    (clement_iff_fig6 w w').2 ((theorem_4_14 n).complete (by rw [lift_tr, lift_tr]; exact h))
  surjective := lemma_1_4 n

end QCert.Clement2019
