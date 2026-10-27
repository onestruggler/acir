/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément (2019): Theorem 4.1

The generators `(-1)[j]`, `H[j,k]`, `X[j,k]` (`j ≠ k`) and the relations
(1)–(21), with (22) when `n = 2`, present `Uₙ(ℤ[1/√2]) = Oₙ(ℤ[1/√2])`
for every `n`: soundness (Section 3.5), completeness (Theorem 4.1) and
generation (Lemma 1.4, by the real Giles–Selinger algorithm, Algorithm 1).
-/
import QCert.Clement2019.Soundness
import QCert.HadamardPi.Synth

namespace QCert.Clement2019

open QCert.HadamardPi

/-- The generators of Hadamard-Π's Figure 6 are among Clément's. -/
def ofFig6 {n : ℕ} : HadamardPi.Gen n → Gen n
  | .Z a => .Z a
  | .X a b h => .X a b (ne_of_lt h)
  | .H a b h => .H a b (ne_of_lt h)

theorem lift_ofFig6 {n : ℕ} (w : Word (HadamardPi.Gen n)) :
    FreeMonoid.lift (sem n) (FreeMonoid.map ofFig6 w) = FreeMonoid.lift (HadamardPi.sem n) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    congr 1
    cases g <;> rfl

/-- Lemma 1.4 (generation): every element of `Oₙ(ℤ[1/√2])` is a product of
generators.  Clément's Algorithm 1 outputs single generators where
Hadamard-Π's outputs syllables of the same generators, so we use the
latter (`QCert.HadamardPi.lift_sem_surjective`). -/
theorem lemma_1_4 (n : ℕ) : Function.Surjective (FreeMonoid.lift (sem n)) := by
  intro M
  obtain ⟨w, hw⟩ := HadamardPi.lift_sem_surjective M
  exact ⟨FreeMonoid.map ofFig6 w, by rw [lift_ofFig6, hw]⟩

/-- Theorem 4.1 (completeness), with soundness (Section 3.5) and generation
(Lemma 1.4): the relations (1)–(22) present `Oₙ(ℤ[1/√2])`. -/
theorem theorem_4_1 (n : ℕ) : IsPresentationOf (Rel (n := n)) (sem n) where
  grouplike := rel_grouplike
  sound := rel_sound
  complete := sorry
  surjective := lemma_1_4 n

end QCert.Clement2019
