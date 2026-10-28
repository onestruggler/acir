/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CliffCS₂ on three wires: the encoding preserves the semantics

Each generator's encoding has the generator's matrix, decided over `ℚ(ω)`
(`e_ok`).  The encodings of the swaps are products of three CNOTs
`K_t CS CS K_t i`, whose matrices are first identified with permutation
matrices (`cx₁₂`, …), which keeps the decisions small.
-/
import QCert.Minimality.CliffordCS.W3Base

namespace QCert.Minimality.CliffordCS.W3

open Matrix QCert.Circuit OmegaParity

theorem ofMat_eq_of {R : Type*} {k : ℕ} {M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R} {N : Op R 2 k}
    (h : ∀ i j : Fin (2 ^ k), M i j = N (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)) :
    ofMat M = N := by
  ext s t
  have := h (finFunctionFinEquiv s) (finFunctionFinEquiv t)
  simpa [ofMat] using this

/-- The permutation matrix of `f` (`e_j ↦ e_{f j}`). -/
def permMat (f : Fin 8 → Fin 8) : Matrix (Fin 8) (Fin 8) QOmega := fun i j => if f j = i then 1 else 0

/-- The CNOT with control qubit `1` and target qubit `2` (index `4 q₀ + 2 q₁ + q₂`). -/
theorem cx₁₂ : FreeMonoid.lift (matR matS) (cxw .CS₁₂ .K₂) = permMat ![0, 1, 3, 2, 4, 5, 7, 6] := by
  decide +kernel

/-- The CNOT with control qubit `2` and target qubit `1`. -/
theorem cx₂₁ : FreeMonoid.lift (matR matS) (cxw .CS₁₂ .K₁) = permMat ![0, 3, 2, 1, 4, 7, 6, 5] := by
  decide +kernel

/-- The CNOT with control qubit `0` and target qubit `1`. -/
theorem cx₀₁ : FreeMonoid.lift (matR matS) (cxw .CS₀₁ .K₁) = permMat ![0, 1, 2, 3, 6, 7, 4, 5] := by
  decide +kernel

/-- The CNOT with control qubit `1` and target qubit `0`. -/
theorem cx₁₀ : FreeMonoid.lift (matR matS) (cxw .CS₀₁ .K₀) = permMat ![0, 1, 6, 7, 4, 5, 2, 3] := by
  decide +kernel

-- The fourteen kernel decisions share one elaboration budget.
set_option maxHeartbeats 1000000 in
theorem e_ok : ∀ g : QCert.Gen Gate 3,
    ofMat (d := 2) (k := 3) (FreeMonoid.lift (matR matS) (e g)) =
      QOmega.invSqrt2 ^ scaled.exGen g • (scaled.ops.gen g).map ZOmega.toQ
  | .gate0 .ω => ofMat_eq_of (by decide +kernel)
  | .gate1 .H => ofMat_eq_of (by decide +kernel)
  | .gate1 .S => ofMat_eq_of (by decide +kernel)
  | .gate2 .CS => ofMat_eq_of (by decide +kernel)
  | .gate2 .swap => by
    simp only [e, map_mul, cx₁₂, cx₂₁]
    exact ofMat_eq_of (by decide +kernel)
  | .up (.gate0 .ω) => ofMat_eq_of (by decide +kernel)
  | .up (.gate1 .H) => ofMat_eq_of (by decide +kernel)
  | .up (.gate1 .S) => ofMat_eq_of (by decide +kernel)
  | .up (.gate2 .CS) => ofMat_eq_of (by decide +kernel)
  | .up (.gate2 .swap) => by
    simp only [e, map_mul, cx₀₁, cx₁₀]
    exact ofMat_eq_of (by decide +kernel)
  | .up (.up (.gate0 .ω)) => ofMat_eq_of (by decide +kernel)
  | .up (.up (.gate1 .H)) => ofMat_eq_of (by decide +kernel)
  | .up (.up (.gate1 .S)) => ofMat_eq_of (by decide +kernel)
  | .up (.up (.up (.gate0 .ω))) => ofMat_eq_of (by decide +kernel)

end QCert.Minimality.CliffordCS.W3
