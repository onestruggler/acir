/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# RCliff₂ and Makary–Ross–Selinger's presentation: encoding and decoding

Makary, Ross and Selinger's presentation of real stabilizer circuits
(`QCert.RealStabilizer`) has the generators `-1`, `H`, `Z` and `CZ`, no
swap, and real orthogonal matrices.  The encoding `E` (Table 3) writes the
CNOT as `H CZ H` on its target and the swap as `(H ⊗ H) CZ (H ⊗ H) CZ (H ⊗ H)
CZ`; the decoding `D` writes `CZ` as `H CNOT H` on wire `0`.  `E` preserves
the semantics (`sem_E`), the source's matrices read over `ℂ` (`Sc`).
-/
import QCert.Minimality.RealClifford.Semantics
import QCert.Minimality.Cross
import QCert.RealStabilizer.Semantics

namespace QCert.Minimality.RealClifford

open Matrix Qubit

namespace Src

open QCert.RealStabilizer in
/-- The source gates over ℤ[ω], the Hadamard scaled by `√2`. -/
def ops : GateOps QCert.RealStabilizer.Gate ZOmega 2 where
  scalar _ := -1
  gate1
    | .H => hadZ
    | .Z => zZ
  gate2
    | .CZ => czZ
  gate3 g := nomatch g

/-- The scaling of the source gates: only `H` carries a factor `1/√2`. -/
def scaled : ScaledOps QCert.RealStabilizer.Gate ZOmega 2 where
  ops := ops
  e1
    | .H => 1
    | .Z => 0
  e2 _ := 0
  e3 g := nomatch g

/-- The source semantics read over `ℂ`. -/
noncomputable def Sc : GateSem QCert.RealStabilizer.Gate ℂ 2 where
  scalar
    | .neg => ⟨-1, minus_one_mem⟩
  gate1
    | .H => ⟨hadamardC, hadamardC_mem⟩
    | .Z => ⟨zC, zC_mem⟩
  gate2
    | .CZ => ⟨czC, czC_mem⟩
  gate3 g := nomatch g

theorem matH_eq : (ofMat QCert.RealStabilizer.matH).map Complex.ofRealHom = hadamardC := by
  ext s t
  rw [Matrix.map_apply, ofMat1]
  simp only [hadamardC]
  generalize s 0 = a
  generalize t 0 = b
  fin_cases a <;> fin_cases b <;> simp [QCert.RealStabilizer.matH]

theorem matZ_eq : (ofMat QCert.RealStabilizer.matZ).map Complex.ofRealHom = zC := by
  ext s t
  rw [Matrix.map_apply, ofMat1]
  simp only [zC]
  generalize s 0 = a
  generalize t 0 = b
  fin_cases a <;> fin_cases b <;> simp [QCert.RealStabilizer.matZ]

theorem matCZ_eq : (ofMat QCert.RealStabilizer.matCZ).map Complex.ofRealHom = czC := by
  ext s t
  rw [Matrix.map_apply, ofMat2]
  simp only [czC]
  generalize s 0 = a
  generalize s 1 = b
  generalize t 0 = c
  generalize t 1 = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [QCert.RealStabilizer.matCZ, pair]

/-- `Sc` is the source semantics read over `ℂ`. -/
theorem Sc_toOps : Sc.toOps = QCert.RealStabilizer.S.toOps.map Complex.ofRealHom := by
  simp only [GateSem.toOps, GateOps.map]
  congr 1
  · funext c; cases c; show (-1 : ℂ) = Complex.ofRealHom (-1); simp
  · funext g; cases g
    · exact matH_eq.symm
    · exact matZ_eq.symm
  · funext g; cases g
    exact matCZ_eq.symm
  · funext g; exact nomatch g

theorem sem_Sc {n : ℕ} (w : Circuit QCert.RealStabilizer.Gate n) :
    (Sc.sem n w : Op ℂ 2 n) = (QCert.RealStabilizer.S.sem n w : Op ℝ 2 n).map Complex.ofRealHom :=
  GateSem.sem_map_of _ _ _ Sc_toOps w

theorem Sc_scaled : Sc.toOps = scaled.toOps ZOmega.toC invSqrt2 := by
  simp only [GateSem.toOps, ScaledOps.toOps]
  congr 1
  · funext c; cases c; show (-1 : ℂ) = ZOmega.toC (-1); simp
  · funext g; cases g
    · exact hadamardC_eq
    · exact zC_eq
  · funext g; cases g
    exact czC_eq
  · funext g; exact nomatch g

end Src

open QCert.RealStabilizer (tseq)

/-- The encoding (Table 3): RCliff₂ circuits as Makary–Ross–Selinger's. -/
def E : GateSubst Gate QCert.RealStabilizer.Gate where
  φ0 _ := QCert.RealStabilizer.mone
  φ1
    | .H => QCert.RealStabilizer.H₀
    | .Z => QCert.RealStabilizer.Z₀
  φ2
    | .CX => tseq [QCert.RealStabilizer.H₀, QCert.RealStabilizer.CZ₀₁, QCert.RealStabilizer.H₀]
    | .swap => tseq [QCert.RealStabilizer.H₀, QCert.RealStabilizer.H₁,
        QCert.RealStabilizer.CZ₀₁, QCert.RealStabilizer.H₀, QCert.RealStabilizer.H₁,
        QCert.RealStabilizer.CZ₀₁, QCert.RealStabilizer.H₀, QCert.RealStabilizer.H₁,
        QCert.RealStabilizer.CZ₀₁]
  φ3 g := nomatch g

/-- The decoding (Table 3): Makary–Ross–Selinger's circuits as RCliff₂'s. -/
def D : GateSubst QCert.RealStabilizer.Gate Gate where
  φ0 _ := minus
  φ1
    | .H => H
    | .Z => Z
  φ2
    | .CZ => seq [H₀, CX, H₀]
  φ3 g := nomatch g

/-- The encoding preserves the semantics, gate by gate. -/
theorem sem_E {n : ℕ} (w : Circuit Gate n) : Src.Sc.sem n (E.map n w) = sem.sem n w := by
  refine E.sem_map sem Src.Sc (fun c => ?_) (fun c => ?_) (fun c => ?_)
    (fun c => nomatch c) w <;> apply Subtype.ext <;>
    refine sem_eq_cross _ Src.scaled Src.Sc_scaled _ scaled sem_toOps ?_ <;>
    (cases c <;> decide +kernel)

/-- The source's real matrix of an encoded circuit, read over `ℂ`, is the
circuit's matrix. -/
theorem sem_E_real {n : ℕ} (w : Circuit Gate n) :
    (QCert.RealStabilizer.S.sem n (E.map n w) : Op ℝ 2 n).map Complex.ofRealHom =
      (sem.sem n w : Op ℂ 2 n) := by
  rw [← Src.sem_Sc, sem_E]

end QCert.Minimality.RealClifford
