/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): the gate matrices

The gates of Section 3 as operators on the basis states `|x₀ x₁ x₂⟩` of
three qubits, qubit `0` first; read as `8 × 8` matrices with `|x₀ x₁ x₂⟩`
the basis vector `4 x₀ + 2 x₁ + x₂`.  The matrices are defined over any
commutative ring with an element `s` standing for `1/√2`; the semantics
takes `ℝ` and `s = 1/√2`, and lands in `O(8, 𝔻) = O_8(ℤ[1/2])` for `Σ₁`
(Theorem 5.2) and in `TofH(3) = L₈`, the orthogonal matrices `N/√2^k`, for
`Σ₂` (Theorem 6.3).
-/
import QCert.ToffoliHadamard.Syntax
import QCert.LiRossSelinger.Semantics

namespace QCert.ToffoliHadamard

open Matrix

variable {R : Type*} [CommRing R]

/-- Basis states `|x₀ x₁ x₂⟩` of three qubits. -/
abbrev State := Fin 3 → Fin 2

/-- The basis vector of `|x₀ x₁ x₂⟩` is `4 x₀ + 2 x₁ + x₂`. -/
def stateIdx : State ≃ Fin 8 where
  toFun x := ⟨4 * x 0 + 2 * x 1 + x 2, by omega⟩
  invFun i := ![⟨i / 4 % 2, by omega⟩, ⟨i / 2 % 2, by omega⟩, ⟨i % 2, by omega⟩]
  left_inv x := by
    funext j
    fin_cases j <;> apply Fin.ext <;> simp <;> omega
  right_inv i := by
    ext; simp; omega

/-- An operator on three qubits as an `8 × 8` matrix. -/
def toMat8 (A : Matrix State State R) : Matrix (Fin 8) (Fin 8) R :=
  A.submatrix stateIdx.symm stateIdx.symm

/-- `X`. -/
def matX : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- `Z`. -/
def matZ : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]

/-- `H = s [[1, 1], [1, −1]]` (`s = 1/√2`). -/
def matH (s : R) : Matrix (Fin 2) (Fin 2) R := !![s, s; s, -s]

/-- `M_j`: the one-qubit matrix `M` on qubit `j`. -/
def onQ (j : Fin 3) (M : Matrix (Fin 2) (Fin 2) R) : Matrix State State R :=
  fun y x => if ∀ k, k ≠ j → y k = x k then M (y j) (x j) else 0

/-- `CM_{j,k}`: `|x⟩ ↦ (M_k)^{x_j} |x⟩`. -/
def ctrl (j k : Fin 3) (M : Matrix (Fin 2) (Fin 2) R) : Matrix State State R :=
  fun y x => if x j = 1 then onQ k M y x else if y = x then 1 else 0

/-- `CCM_{j,k}`: `|x⟩ ↦ (M_l)^{x_j x_k} |x⟩`, `l` the third qubit. -/
def ctrl2 (j k l : Fin 3) (M : Matrix (Fin 2) (Fin 2) R) : Matrix State State R :=
  fun y x => if x j = 1 ∧ x k = 1 then onQ l M y x else if y = x then 1 else 0

/-- `σ_{j,k}`: exchanges qubits `j` and `k` (`= CX_{j,k} CX_{k,j} CX_{j,k}`). -/
def swapQ (j k : Fin 3) : Matrix State State R :=
  fun y x => if y = x ∘ Equiv.swap j k then 1 else 0

/-- `K_{j,k} = H_j H_k`: `H` on qubits `j` and `k`. -/
def kQ (j k : Fin 3) (s : R) : Matrix State State R :=
  fun y x => if ∀ l, l ≠ j → l ≠ k → y l = x l then matH s (y j) (x j) * matH s (y k) (x k) else 0

/-- `K = H ⊗ H` as a `4 × 4` matrix (entries `±s² = ±1/2`). -/
def matK (s : R) : Matrix (Fin 4) (Fin 4) R :=
  fun i j => if ((i : ℕ) / 2 = 1 ∧ (j : ℕ) / 2 = 1) ≠ ((i : ℕ) % 2 = 1 ∧ (j : ℕ) % 2 = 1)
    then -(s * s) else s * s

/-- The matrix of a letter of `Σ₁` (over `R`, with `s = 1/√2`). -/
def gateMat (s : R) : Sym1 → Matrix (Fin 8) (Fin 8) R
  | .X0 => toMat8 (onQ 0 matX)
  | .X1 => toMat8 (onQ 1 matX)
  | .X2 => toMat8 (onQ 2 matX)
  | .CX01 => toMat8 (ctrl 0 1 matX)
  | .CX02 => toMat8 (ctrl 0 2 matX)
  | .CX10 => toMat8 (ctrl 1 0 matX)
  | .CX12 => toMat8 (ctrl 1 2 matX)
  | .CX20 => toMat8 (ctrl 2 0 matX)
  | .CX21 => toMat8 (ctrl 2 1 matX)
  | .CCX01 => toMat8 (ctrl2 0 1 2 matX)
  | .CCX02 => toMat8 (ctrl2 0 2 1 matX)
  | .CCX12 => toMat8 (ctrl2 1 2 0 matX)
  | .Z0 => toMat8 (onQ 0 matZ)
  | .Z1 => toMat8 (onQ 1 matZ)
  | .Z2 => toMat8 (onQ 2 matZ)
  | .CZ01 => toMat8 (ctrl 0 1 matZ)
  | .CZ02 => toMat8 (ctrl 0 2 matZ)
  | .CZ12 => toMat8 (ctrl 1 2 matZ)
  | .K01 => toMat8 (kQ 0 1 s)
  | .K12 => toMat8 (kQ 1 2 s)
  | .S01 => toMat8 (swapQ 0 1)
  | .S02 => toMat8 (swapQ 0 2)
  | .S12 => toMat8 (swapQ 1 2)
  | .Kc => levelMat ![0, 1, 2, 3] (matK s)
  | .CCZ => toMat8 (ctrl2 0 1 2 matZ)

/-- The matrix of `H₂`. -/
def matH2 (s : R) : Matrix (Fin 8) (Fin 8) R := toMat8 (onQ 2 (matH s))

end QCert.ToffoliHadamard
