/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: semantics

Translation of `Semantics.agda`.  A circuit over `Σ₁` (in particular a
Toffoli-K circuit) denotes an orthogonal `8 × 8` matrix over `𝔻 = ℤ[1/2]`,
an element of the group `O(8, 𝔻)` of Li–Ross–Selinger (`O_ZHalf 8`); a
circuit over `Σ₂` denotes an orthogonal scaled dyadic matrix, an element of
the group `L₈ = TofH(3)` of Li–Ross–Selinger's §5 (`LiRossSelinger.L 8`).
In both cases the value is that of the circuit's encoding (`Encoding`), so
the semantics is a monoid homomorphism by construction, and
`GateMatrices` checks that each gate denotes its usual matrix.
-/
import QCert.ToffoliHadamardRS.Encoding
import QCert.LiRossSelinger.Semantics

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (Gen GenL)

noncomputable section

variable {k : ℕ}

/-! ## In `O(8, 𝔻)` -/

/-- The group `O(8, 𝔻)`. -/
abbrev O8 : Subgroup (Matrix.unitaryGroup (Fin 8) ℝ) := O_ZHalf 8

/-- The value of a circuit at any level (`H₂` read as `ε`): the value of its
encoding (the Agda's `⟦_⟧`). -/
def semO : Word (Gate k) →* O8 := (FreeMonoid.lift (LiRossSelinger.sem 8)).comp encW

/-- The semantics of `Σ₁` in `O(8, 𝔻)`. -/
def sem1 (g : G₁) : O8 := FreeMonoid.lift (LiRossSelinger.sem 8) (enc g)

theorem lift_sem1 (w : Word G₁) : FreeMonoid.lift sem1 w = semO w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih => rw [map_mul, map_mul, ih, FreeMonoid.lift_eval_of]; simp [semO, sem1]

/-! ## In `TofH(3) = L₈` -/

/-- The group `L₈`. -/
abbrev TofH3 : Subgroup (Matrix.unitaryGroup (Fin 8) ℝ) := LiRossSelinger.L 8

/-- The value of a circuit at any level in `L₈`. -/
def semH : Word (Gate k) →* TofH3 := (FreeMonoid.lift (LiRossSelinger.semL 4)).comp encLW

/-- The semantics of `Σ₂` in `TofH(3)`. -/
def sem2 (g : G₂) : TofH3 := FreeMonoid.lift (LiRossSelinger.semL 4) (encL g)

theorem lift_sem2 (w : Word G₂) : FreeMonoid.lift sem2 w = semH w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih => rw [map_mul, map_mul, ih, FreeMonoid.lift_eval_of]; simp [semH, sem2]

end

end QCert.ToffoliHadamardRS
