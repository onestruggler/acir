/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Translating between Clément's generators and those of Figure 6

The generators of Figure 6 (`QCert.HadamardPi.Gen`, two-level generators on
increasing indices) are among Clément's (`Gen`, any two distinct indices):
`ι` is the inclusion.  Conversely `tr` writes a Clément generator with
decreasing indices through increasing ones, `X[k,j] = X[j,k]` and
`H[k,j] = X[j,k] H[j,k] X[j,k]` for `j < k` (Lemma 1.7 of Clément's notes,
relation (e2) of Hadamard-Π's appendix).  Both preserve the matrices
(`lift_ι`, `lift_tr`), and `tr ∘ ι` is the identity (`tr_ι`).
-/
import QCert.Clement2019.Soundness

namespace QCert.Clement2019

open Matrix QCert.HadamardPi

variable {n : ℕ}

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

/-- The inclusion of words over `𝒢ₙ`. -/
def ι : Word (HadamardPi.Gen n) →* Word (Gen n) := FreeMonoid.map ofFig6

/-- A Clément generator as a word over `𝒢ₙ`. -/
def trg : Gen n → Word (HadamardPi.Gen n)
  | .Z j => FreeMonoid.of (.Z j)
  | .X j k h =>
    if hjk : j < k then FreeMonoid.of (.X j k hjk)
    else FreeMonoid.of (.X k j (lt_of_le_of_ne (not_lt.1 hjk) (Ne.symm h)))
  | .H j k h =>
    if hjk : j < k then FreeMonoid.of (.H j k hjk)
    else
      have hkj : k < j := lt_of_le_of_ne (not_lt.1 hjk) (Ne.symm h)
      FreeMonoid.of (.X k j hkj) * FreeMonoid.of (.H k j hkj) * FreeMonoid.of (.X k j hkj)

/-- Clément words written over `𝒢ₙ`. -/
def tr : Word (Gen n) →* Word (HadamardPi.Gen n) := FreeMonoid.lift trg

theorem lift_ι (w : Word (HadamardPi.Gen n)) :
    FreeMonoid.lift (sem n) (ι w) = FreeMonoid.lift (HadamardPi.sem n) w := lift_ofFig6 w

theorem lift_tr (w : Word (Gen n)) :
    FreeMonoid.lift (HadamardPi.sem n) (tr w) = FreeMonoid.lift (sem n) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    congr 1
    apply Subtype.ext; apply Subtype.ext
    rw [HadamardPi.lift_sem_val]
    show HadamardPi.wordMat invSqrt2 (trg g) = LGen.mat invSqrt2 g.toL
    cases g with
    | Z j => simp [trg, HadamardPi.wordMat, genMat, Gen.toL, LGen.mat]
    | X j k h =>
      simp only [trg]
      split_ifs with hjk
      · simp [HadamardPi.wordMat, genMat, Gen.toL, LGen.mat]
      · have hkj : k < j := lt_of_le_of_ne (not_lt.1 hjk) (Ne.symm h)
        rw [show (LGen.mat invSqrt2 (Gen.X j k h).toL : Matrix (Fin n) (Fin n) ℝ) =
          lprod invSqrt2 ([LGen.X 1 0].map (LGen.push ![k, j])) by simp [lprod, Gen.toL, LGen.push]]
        rw [lprod_push _ (by vec_inj), ← lprod_eq_of_check [.X 0 1] [.X 1 0] (by decide +kernel),
          ← lprod_push _ (by vec_inj)]
        simp [lprod, HadamardPi.wordMat, genMat_eq, HadamardPi.Gen.toL, LGen.push]
    | H j k h =>
      simp only [trg]
      split_ifs with hjk
      · simp [HadamardPi.wordMat, genMat, Gen.toL, LGen.mat]
      · have hkj : k < j := lt_of_le_of_ne (not_lt.1 hjk) (Ne.symm h)
        rw [show (LGen.mat invSqrt2 (Gen.H j k h).toL : Matrix (Fin n) (Fin n) ℝ) =
          lprod invSqrt2 ([LGen.H 1 0].map (LGen.push ![k, j])) by simp [lprod, Gen.toL, LGen.push]]
        rw [lprod_push _ (by vec_inj),
          ← lprod_eq_of_check [.X 0 1, .H 0 1, .X 0 1] [.H 1 0] (by decide +kernel),
          ← lprod_push _ (by vec_inj)]
        simp [lprod, HadamardPi.wordMat, genMat_eq, HadamardPi.Gen.toL, LGen.push, Matrix.mul_assoc]

/-- Writing an included word back over `𝒢ₙ` gives the word itself. -/
theorem tr_ι (w : Word (HadamardPi.Gen n)) : tr (ι w) = w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, map_mul, ih]
    congr 1
    cases g with
    | Z a => rfl
    | X a b h => simp [ι, tr, ofFig6, trg, h]
    | H a b h => simp [ι, tr, ofFig6, trg, h]

end QCert.Clement2019
