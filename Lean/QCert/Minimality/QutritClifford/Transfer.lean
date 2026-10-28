/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Cliff₃ and the refined qutrit presentation: encoding and decoding

The encoding `E` and decoding `D` of Table 3 between Cliff₃ and the refined
source (`Refine`): `ω₁₂ ↦ ω₁₂`, `S ↦ S² ω₁₂⁴` both ways, the CNOT encoded
as `H CZ H³` on its target and `CZ` decoded as `H³ CNOT H` on the lower
wire, the swap encoded by Li et al.'s swap (D6) times `ω₁₂³⁰ = -1`.  The
Hadamard gates differ by a phase: Li et al.'s `H` is `(ω² - ω)⁻¹ [ωʲᵏ]`,
`i` times the `H` of Definition 17, so `D(H) = H ω₁₂³` and `E(H) = H ω₁₂⁹`.
Table 3 prints these two phases the other way round (`D(H) = H ω₁₂⁹`,
`E(H) = H ω₁₂³`), which would not preserve the semantics; the decoded
relation C4 fails with the printed `D`.

`E` preserves the semantics (`sem_E`), decided over ℤ[ζ₁₂] on row tries
for each gate, the refined source's matrices being written as scaled ℤ[ζ₁₂]
matrices through Li et al.'s own matrices over `ℚ(ζ)`.
-/
import QCert.Minimality.QutritClifford.Refine

namespace QCert.Minimality.QutritClifford

open Matrix Qutrit QCert.Circuit

namespace Src

/-- `√3 H`, `S` and `CZ` of the refined source over ℤ[ζ₁₂]. -/
def hzR : Op ZZeta 3 1 := fun s t => ZZeta.ζ ^ 3 * ZZeta.ζ ^ (4 * ((s 0 : ℕ) * (t 0 : ℕ)))
def szR : Op ZZeta 3 1 := fun s t =>
  if s 0 = t 0 then (if (s 0 : ℕ) = 2 then 1 else ZZeta.ζ ^ 4) else 0
def czR : Op ZZeta 3 2 := fun s t =>
  if s 0 = t 0 ∧ s 1 = t 1 then ZZeta.ζ ^ (4 * ((s 0 : ℕ) * (s 1 : ℕ))) else 0

/-- The refined source's gates over ℤ[ζ₁₂], `H` scaled by `√3`. -/
def ops : GateOps RGate ZZeta 3 where
  scalar _ := ZZeta.ζ
  gate1
    | .H => hzR
    | .S => szR
  gate2
    | .CZ => czR
  gate3 g := nomatch g

def scaled : ScaledOps RGate ZZeta 3 where
  ops := ops
  e1
    | .H => 1
    | .S => 0
  e2 _ := 0
  e3 g := nomatch g

/-- `1/√3` in `ℚ(ζ)`: `(2ζ - ζ³)/3`. -/
def c3 : QCert.QutritClifford.Q := ⟨0, 2 / 3, 0, -1 / 3⟩

theorem toC_toQ (x : ZZeta) : QCert.QutritClifford.toC (ZZeta.toQ x) = ZZeta.toC x := by
  have : QCert.QutritClifford.toC.comp ZZeta.toQ = ZZeta.toC := by
    refine ZQuartic.hom_ext (R := ℂ) ?_
    rw [RingHom.comp_apply, ZZeta.toC_X, ← ζ_eq,
      show ZZeta.toQ ZQuartic.X = Quartic.X from ZQuartic.lift_X _ _]
    exact Quartic.lift_X _ _
  exact congrArg (fun f : ZZeta →+* ℂ => f x) this

theorem toC_c3 : QCert.QutritClifford.toC c3 = invSqrt3 := by
  have hc : c3 = ZZeta.toQ ZZeta.sqrt3 * Quartic.ofRat (1 / 3) := by decide +kernel
  have hr : Real.sqrt 3 * (1 / 3) = (Real.sqrt 3)⁻¹ := by
    have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hne : Real.sqrt 3 ≠ 0 := by positivity
    field_simp
    linarith
  have hq : QCert.QutritClifford.toC (Quartic.ofRat (1 / 3)) = ((1 / 3 : ℚ) : ℂ) :=
    Quartic.lift_ofRat _ _ _
  rw [hc, map_mul, toC_toQ, ZZeta.toC_sqrt3, hq, invSqrt3,
    show ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ = (((Real.sqrt 3)⁻¹ : ℝ) : ℂ) by push_cast; rfl, ← hr]
  push_cast
  ring

theorem HQ_eq : (ofMat (k := 1) QCert.QutritClifford.HQ : Op QCert.QutritClifford.Q 3 1) =
    c3 • hzR.map ZZeta.toQ := by
  funext s t
  rw [ofMat3_1]
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hzR]
  generalize s 0 = a
  generalize t 0 = b
  revert a b
  decide +kernel

theorem SQ_eq : (ofMat (k := 1) QCert.QutritClifford.SQ : Op QCert.QutritClifford.Q 3 1) =
    szR.map ZZeta.toQ := by
  funext s t
  rw [ofMat3_1]
  simp only [Matrix.map_apply, szR]
  generalize s 0 = a
  generalize t 0 = b
  revert a b
  decide +kernel

theorem CZQ_eq : (ofMat (k := 2) QCert.QutritClifford.CZQ : Op QCert.QutritClifford.Q 3 2) =
    czR.map ZZeta.toQ := by
  funext s t
  rw [ofMat3_2]
  simp only [Matrix.map_apply, czR]
  generalize s 0 = a
  generalize s 1 = b
  generalize t 0 = c
  generalize t 1 = d
  revert a b c d
  decide +kernel

theorem RS_toOps : RS.toOps = scaled.toOps ZZeta.toC invSqrt3 := by
  simp only [GateSem.toOps, ScaledOps.toOps]
  congr 1
  · funext c; cases c; exact ZZeta.toC_X.symm
  · funext g; cases g
    · show ofMat (d := 3) (k := 1) QCert.QutritClifford.Hmat = _
      rw [← QCert.QutritClifford.HQ_map, ← QCert.QutritClifford.ofMat_map, HQ_eq]
      funext s t
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, toC_toQ, toC_c3]
      show _ = invSqrt3 ^ 1 * _
      rw [pow_one]
      rfl
    · show ofMat (d := 3) (k := 1) QCert.QutritClifford.Smat = _
      rw [← QCert.QutritClifford.SQ_map, ← QCert.QutritClifford.ofMat_map, SQ_eq]
      funext s t
      simp [Matrix.map_apply, toC_toQ, scaled, ops]
  · funext g; cases g
    show ofMat (d := 3) (k := 2) QCert.QutritClifford.CZmat = _
    rw [← QCert.QutritClifford.CZQ_map, ← QCert.QutritClifford.ofMat_map, CZQ_eq]
    funext s t
    simp [Matrix.map_apply, toC_toQ, scaled, ops]
  · funext g; exact nomatch g

end Src

/-- The encoding: Cliff₃ circuits as refined source circuits. -/
def E : GateSubst Gate RGate where
  φ0 _ := g0 RGate.w
  φ1
    | .H => g0 RGate.w ^ 9 * g1 RGate.H
    | .S => g0 RGate.w ^ 4 * (g1 RGate.S * g1 RGate.S)
  φ2
    | .CX => seq [g1 RGate.H, g2 RGate.CZ, g1 RGate.H, g1 RGate.H, g1 RGate.H]
    | .swap => seq [g1 RGate.H, shift (g1 RGate.H), g2 RGate.CZ, g1 RGate.H, shift (g1 RGate.H),
        g2 RGate.CZ, g1 RGate.H, shift (g1 RGate.H), g2 RGate.CZ, g0 RGate.w ^ 30]
  φ3 g := nomatch g

/-- The decoding: refined source circuits as Cliff₃ circuits. -/
def D : GateSubst RGate Gate where
  φ0 _ := ω
  φ1
    | .H => ω ^ 3 * H
    | .S => ω ^ 4 * (S * S)
  φ2
    | .CZ => seq [H₀, H₀, H₀, CX, H₀]
  φ3 g := nomatch g

/-- The encoding preserves the semantics, gate by gate. -/
theorem sem_E {n : ℕ} (w : Circuit Gate n) : RS.sem n (E.map n w) = sem.sem n w := by
  refine E.sem_map sem RS (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c => nomatch c) w <;>
    apply Subtype.ext <;>
    refine sem_eq_cross3 _ Src.scaled Src.RS_toOps _ scaled sem_toOps ?_ <;>
    (cases c <;> decide +kernel)

end QCert.Minimality.QutritClifford
