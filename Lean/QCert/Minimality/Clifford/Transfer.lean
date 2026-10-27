/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Cliff₂ and Selinger's presentation: encoding and decoding (Table 3)

Selinger's presentation of Clifford circuits (`QCert.SelingerClifford`) has
the generators `ω`, `H`, `S` and the controlled-`Z` `Z_c`, and no swap.  The
encoding `E` (Table 3) writes the CNOT as `H Z_c H` on its target, and the
swap as `(H ⊗ H) Z_c (H ⊗ H) Z_c (H ⊗ H) Z_c` (the circuit of the paper's
decoding of (DSWAPdef), Appendix G.1); the decoding `D` writes `Z_c` as
`H CNOT H` on wire `0`.  Both fix `ω`, `H` and `S`.  `E` preserves the
semantics (`sem_E`), decided over ℤ[ω] on row tries for each gate.
-/
import QCert.Minimality.Clifford.Semantics
import QCert.Minimality.Cross
import QCert.SelingerClifford.Semantics

namespace QCert.Minimality.Clifford

open Matrix Qubit

namespace Sel

open QCert.SelingerClifford in
/-- Selinger's gates over ℤ[ω], the Hadamard scaled by `√2`. -/
def ops : GateOps QCert.SelingerClifford.Gate ZOmega 2 where
  scalar _ := ZOmega.ω
  gate1
    | .H => hadZ
    | .S => sZ
  gate2
    | .CZ => fun s t => if s 0 = t 0 ∧ s 1 = t 1 then (-1) ^ ((s 0 : ℕ) * (s 1 : ℕ)) else 0
  gate3 g := nomatch g

/-- The scaling of Selinger's gates: only `H` carries a factor `1/√2`. -/
def scaled : ScaledOps QCert.SelingerClifford.Gate ZOmega 2 where
  ops := ops
  e1
    | .H => 1
    | .S => 0
  e2 _ := 0
  e3 g := nomatch g

theorem matH_eq : ofMat QCert.SelingerClifford.matH = hadamardC := by
  ext s t
  rw [ofMat1]
  simp only [hadamardC]
  generalize s 0 = a
  generalize t 0 = b
  fin_cases a <;> fin_cases b <;> simp [QCert.SelingerClifford.matH]

theorem matS_eq : ofMat QCert.SelingerClifford.matS = sC := by
  ext s t
  rw [ofMat1]
  simp only [sC]
  generalize s 0 = a
  generalize t 0 = b
  fin_cases a <;> fin_cases b <;> simp [QCert.SelingerClifford.matS]

theorem matCZ_eq : ofMat QCert.SelingerClifford.matCZ =
    invSqrt2 ^ 0 • (ops.gate2 .CZ).map ZOmega.toC := by
  ext s t
  rw [ofMat2]
  simp only [ops, pow_zero, one_smul, Matrix.map_apply]
  generalize s 0 = a
  generalize s 1 = b
  generalize t 0 = c
  generalize t 1 = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [QCert.SelingerClifford.matCZ, pair]

theorem sem_toOps : QCert.SelingerClifford.S.toOps = scaled.toOps ZOmega.toC invSqrt2 := by
  simp only [GateSem.toOps, ScaledOps.toOps]
  congr 1
  · funext c; cases c; exact ZOmega.toC_X.symm
  · funext g; cases g
    · show ofMat QCert.SelingerClifford.matH = _
      rw [matH_eq]; exact hadamardC_eq
    · show ofMat QCert.SelingerClifford.matS = _
      rw [matS_eq]; exact sC_eq
  · funext g; cases g
    exact matCZ_eq
  · funext g; exact nomatch g

end Sel

open QCert.SelingerClifford (tseq)

/-- The encoding (Table 3): Cliff₂ circuits as Selinger's. -/
def E : GateSubst Gate QCert.SelingerClifford.Gate where
  φ0 _ := QCert.SelingerClifford.om
  φ1
    | .H => QCert.SelingerClifford.H₀
    | .S => QCert.SelingerClifford.S₀
  φ2
    | .CX => tseq [QCert.SelingerClifford.H₀, QCert.SelingerClifford.CZ₀₁,
        QCert.SelingerClifford.H₀]
    | .swap => tseq [QCert.SelingerClifford.H₀, QCert.SelingerClifford.H₁,
        QCert.SelingerClifford.CZ₀₁, QCert.SelingerClifford.H₀, QCert.SelingerClifford.H₁,
        QCert.SelingerClifford.CZ₀₁, QCert.SelingerClifford.H₀, QCert.SelingerClifford.H₁,
        QCert.SelingerClifford.CZ₀₁]
  φ3 g := nomatch g

/-- The decoding (Table 3): Selinger's circuits as Cliff₂'s. -/
def D : GateSubst QCert.SelingerClifford.Gate Gate where
  φ0 _ := ω
  φ1
    | .H => H
    | .S => S
  φ2
    | .CZ => seq [H₀, CX, H₀]
  φ3 g := nomatch g

/-- The encoding preserves the semantics, gate by gate. -/
theorem sem_E {n : ℕ} (w : Circuit Gate n) :
    QCert.SelingerClifford.S.sem n (E.map n w) = sem.sem n w := by
  refine E.sem_map sem QCert.SelingerClifford.S (fun c => ?_) (fun c => ?_) (fun c => ?_)
    (fun c => nomatch c) w <;> apply Subtype.ext <;>
    refine sem_eq_cross _ Sel.scaled Sel.sem_toOps _ scaled sem_toOps ?_ <;>
    (cases c <;> decide +kernel)

end QCert.Minimality.Clifford
