/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qutrit Clifford circuits: matrices, the Pauli group and the Clifford group

The gate matrices of §2.1 (Definitions 2.1 and 2.4) over `ℂ`, with the
paper's `ω = e^{2πi/3}` written `ωℂ` here (`ω` is the scalar circuit (D2)):

* `-ω`, a scalar;
* `H = (ω² - ω)⁻¹ [[1, 1, 1], [1, ω, ω²], [1, ω², ω]]`;
* `S = diag(ω, ω, 1)`;
* `CZ = diag(1, 1, 1, 1, ω, ω², 1, ω², ω)`.

A conventional `3^k × 3^k` matrix is read on `k` wires with the top qutrit
the most significant digit (`ofMat`): the paper's `|x, y⟩` is index
`3x + y`, `x` on wire 1 (top) and `y` on wire 0 (bottom).

All entries lie in `ℚ(ζ)`, `ζ = e^{iπ/6}` a primitive twelfth root of unity
(`ω = ζ⁴ = ζ² - 1`), which `Quartic 1 (-1)` computes exactly; `ops` is the
same gate set over it, so equations between circuits are decided there
(`QutritClifford.Vec.eval_eq_of_cols`) and carried to `ℂ`.

The Pauli group `𝒫ₙ` (Definition 2.2) and the Clifford group `𝒞ₙ`
(Definition 2.3, with the restriction of §2.1 to matrices over
`ℤ[1/3, ω]`) are defined here; the theorems about them are in
`QutritClifford.Theorem`.
-/
import QCert.QutritClifford.Syntax
import QCert.Circuit.Eval
import QCert.Exact.Quartic
import QCert.Matrix.Rings
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace QCert.QutritClifford

open Matrix Complex

noncomputable section

/-! ### Roots of unity -/

/-- `ζ = e^{iπ/6} = √3/2 + i/2`, a primitive twelfth root of unity. -/
def ζ : ℂ := ⟨Real.sqrt 3 / 2, 1 / 2⟩

/-- `ωℂ = e^{2πi/3}`, the primitive third root of unity fixed in §2.1. -/
def ωℂ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem ζ_sq : ζ ^ 2 = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
  apply Complex.ext <;> simp [ζ, pow_two] <;> nlinarith [sqrt3_sq]

theorem ζ_pow_four : ζ ^ 4 = ζ ^ 2 - 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ζ_sq]
  apply Complex.ext <;> simp [pow_two] <;> nlinarith [sqrt3_sq]

theorem ζ_pow_three : ζ ^ 3 = Complex.I := by
  rw [pow_succ, ζ_sq]
  apply Complex.ext <;> simp [ζ] <;> nlinarith [sqrt3_sq]

theorem ωℂ_eq : ωℂ = ζ ^ 2 - 1 := by
  have h : (2 * Real.pi * Complex.I / 3 : ℂ) = ((Real.pi - Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ωℂ, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_sub,
    Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three, ζ_sq]
  apply Complex.ext <;> simp <;> norm_num

theorem star_ζ : star ζ = ζ - ζ ^ 3 := by
  rw [ζ_pow_three]
  apply Complex.ext <;> simp [ζ] <;> norm_num

/-! ### `ℚ(ζ)`, computably -/

/-- `ℚ(ζ)`, `ζ⁴ = ζ² - 1`. -/
abbrev Q := Quartic 1 (-1)

/-- `ℚ(ζ)` inside `ℂ`. -/
def toC : Q →+* ℂ := Quartic.lift ζ (by rw [ζ_pow_four]; push_cast; ring)

theorem toC_apply (a : Q) : toC a = a.a0 + a.a1 * ζ + a.a2 * ζ ^ 2 + a.a3 * ζ ^ 3 := rfl

/-- `ωℂ = ζ² - 1` in `ℚ(ζ)`. -/
def ωQ : Q := ⟨-1, 0, 1, 0⟩

/-- `-ωℂ = 1 - ζ²` in `ℚ(ζ)`. -/
def negωQ : Q := ⟨1, 0, -1, 0⟩

/-- `(ωℂ² - ωℂ)⁻¹ = (2ζ² - 1)/3` in `ℚ(ζ)`. -/
def cQ : Q := ⟨-1 / 3, 0, 2 / 3, 0⟩

theorem toC_ωQ : toC ωQ = ωℂ := by
  rw [toC_apply, ωℂ_eq]; simp [ωQ]; ring

theorem toC_negωQ : toC negωQ = -ωℂ := by
  rw [toC_apply, ωℂ_eq]; simp [negωQ]; ring

theorem toC_cQ : toC cQ = (ωℂ ^ 2 - ωℂ)⁻¹ := by
  rw [toC_apply, ωℂ_eq]
  symm
  apply inv_eq_of_mul_eq_one_left
  simp only [cQ]
  push_cast
  linear_combination (2 / 3 * ζ ^ 2 - 5 / 3 : ℂ) * ζ_pow_four

/-- Complex conjugation on `ℚ(ζ)`: `ζ̄ = ζ - ζ³`, `ζ̄² = 1 - ζ²`, `ζ̄³ = -ζ³`. -/
def conjQ (a : Q) : Q := ⟨a.a0 + a.a2, a.a1, -a.a2, -a.a1 - a.a3⟩

theorem toC_conjQ (a : Q) : toC (conjQ a) = star (toC a) := by
  rw [toC_apply, toC_apply]
  simp only [conjQ, star_add, star_mul', star_pow, star_ratCast, star_ζ]
  push_cast
  linear_combination ((a.a2 : ℂ) * (1 - ζ ^ 2) - (a.a3 : ℂ) * (2 * ζ ^ 3 - ζ ^ 5)) * ζ_pow_four

/-- A matrix over `ℚ(ζ)` whose conjugate transpose is a right inverse is
unitary in `ℂ`. -/
theorem map_mem_unitaryGroup {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m Q)
    (h : M * M.transpose.map conjQ = 1) : M.map toC ∈ unitaryGroup m ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
  have : (M.map toC)ᴴ = (M.transpose.map conjQ).map toC := by
    ext i j; simp [conjTranspose_apply, toC_conjQ]
  rw [this, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

/-! ### The gate matrices -/

/-- The Hadamard gate (Definition 2.4). -/
def Hmat : Matrix (Fin 3) (Fin 3) ℂ :=
  (ωℂ ^ 2 - ωℂ)⁻¹ • !![1, 1, 1; 1, ωℂ, ωℂ ^ 2; 1, ωℂ ^ 2, ωℂ]

/-- The phase gate (Definition 2.4). -/
def Smat : Matrix (Fin 3) (Fin 3) ℂ := !![ωℂ, 0, 0; 0, ωℂ, 0; 0, 0, 1]

/-- The controlled-Z gate (Definition 2.4), `CZ |x, y⟩ = ωℂ^{xy} |x, y⟩`. -/
def CZmat : Matrix (Fin 9) (Fin 9) ℂ := Matrix.diagonal ![1, 1, 1, 1, ωℂ, ωℂ ^ 2, 1, ωℂ ^ 2, ωℂ]

/-- `H` over `ℚ(ζ)`. -/
def HQ : Matrix (Fin 3) (Fin 3) Q := cQ • !![1, 1, 1; 1, ωQ, ωQ ^ 2; 1, ωQ ^ 2, ωQ]

/-- `S` over `ℚ(ζ)`. -/
def SQ : Matrix (Fin 3) (Fin 3) Q := !![ωQ, 0, 0; 0, ωQ, 0; 0, 0, 1]

/-- `CZ` over `ℚ(ζ)`. -/
def CZQ : Matrix (Fin 9) (Fin 9) Q := Matrix.diagonal ![1, 1, 1, 1, ωQ, ωQ ^ 2, 1, ωQ ^ 2, ωQ]

theorem HQ_map : HQ.map toC = Hmat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HQ, Hmat, toC_ωQ, toC_cQ, -Quartic.mul_def, -Quartic.zero_def, -Quartic.one_def, -Quartic.add_def, -Quartic.neg_def, -Quartic.sub_def]

theorem SQ_map : SQ.map toC = Smat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SQ, Smat, toC_ωQ, -Quartic.mul_def, -Quartic.zero_def, -Quartic.one_def, -Quartic.add_def, -Quartic.neg_def, -Quartic.sub_def]

theorem CZQ_map : CZQ.map toC = CZmat := by
  ext i j
  rw [map_apply, CZQ, CZmat, diagonal_apply, diagonal_apply]
  split_ifs
  · fin_cases i <;> simp [toC_ωQ, -Quartic.mul_def, -Quartic.zero_def, -Quartic.one_def, -Quartic.add_def, -Quartic.neg_def, -Quartic.sub_def]
  · simp [-Quartic.zero_def]

theorem Hmat_mem : Hmat ∈ unitaryGroup (Fin 3) ℂ := HQ_map ▸ map_mem_unitaryGroup _ (by decide +kernel)

theorem Smat_mem : Smat ∈ unitaryGroup (Fin 3) ℂ := SQ_map ▸ map_mem_unitaryGroup _ (by decide +kernel)

theorem CZmat_mem : CZmat ∈ unitaryGroup (Fin 9) ℂ :=
  CZQ_map ▸ map_mem_unitaryGroup _ (by decide +kernel)

theorem negω_mem : -ωℂ ∈ unitary ℂ := by
  rw [Unitary.mem_iff, ← toC_negωQ, ← toC_conjQ, ← map_mul, ← map_mul]
  constructor <;> rw [show (1 : ℂ) = toC 1 from (map_one _).symm] <;> congr 1 <;> decide +kernel

/-- The matrices of the gates, as unitaries. -/
def gateSem : GateSem Gate ℂ 3 where
  scalar
    | .negω => ⟨-ωℂ, negω_mem⟩
  gate1
    | .H => ⟨ofMat (k := 1) Hmat, ofMat_mem_unitaryGroup Hmat_mem⟩
    | .S => ⟨ofMat (k := 1) Smat, ofMat_mem_unitaryGroup Smat_mem⟩
  gate2
    | .CZ => ⟨ofMat (k := 2) CZmat, ofMat_mem_unitaryGroup CZmat_mem⟩
  gate3 g := nomatch g

/-- The operator of an `n`-qutrit circuit. -/
abbrev sem (n : ℕ) : Circ n →* unitaryGroup (State 3 n) ℂ := gateSem.sem n

end

/-- The gate matrices over `ℚ(ζ)`, computably. -/
def ops : GateOps Gate Q 3 where
  scalar
    | .negω => negωQ
  gate1
    | .H => ofMat (k := 1) HQ
    | .S => ofMat (k := 1) SQ
  gate2
    | .CZ => ofMat (k := 2) CZQ
  gate3 g := nomatch g

theorem ofMat_map {k : ℕ} (M : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) Q) :
    (ofMat M).map toC = ofMat (M.map toC) := rfl

theorem toOps_eq : gateSem.toOps = ops.map toC := by
  simp only [GateSem.toOps, GateOps.map]
  congr 1
  · funext g; cases g; exact toC_negωQ.symm
  · funext g; cases g
    · show ofMat (k := 1) Hmat = ofMat (d := 3) (k := 1) (HQ.map toC); rw [HQ_map]
    · show ofMat (k := 1) Smat = ofMat (d := 3) (k := 1) (SQ.map toC); rw [SQ_map]
  · funext g; cases g
    show ofMat (k := 2) CZmat = ofMat (d := 3) (k := 2) (CZQ.map toC); rw [CZQ_map]
  · funext g; exact nomatch g

/-! ### The Pauli group and the Clifford group -/

noncomputable section

/-- The Pauli `X` gate (Definition 2.1). -/
def Xmat : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- The Pauli `Z` gate (Definition 2.1). -/
def Zmat : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, ωℂ, 0; 0, 0, ωℂ ^ 2]

/-- The Pauli operator `ωℂ^c (X^{a₁} Z^{b₁} ⊗ ⋯ ⊗ X^{aₙ} Z^{bₙ})`: the
entry of a tensor product at `(s, t)` is the product over the wires of
the factors' entries at `(s j, t j)`. -/
def pauli {n : ℕ} (c : Fin 3) (a b : Fin n → Fin 3) : Op ℂ 3 n :=
  fun s t => ωℂ ^ (c : ℕ) * ∏ j, (Xmat ^ (a j : ℕ) * Zmat ^ (b j : ℕ)) (s j) (t j)

/-- The `n`-qutrit Pauli group `𝒫ₙ` (Definition 2.2). -/
def pauliGroup (n : ℕ) : Set (Op ℂ 3 n) :=
  Set.range fun p : Fin 3 × (Fin n → Fin 3) × (Fin n → Fin 3) => pauli p.1 p.2.1 p.2.2

/-- `ℤ[1/3, ωℂ] ⊆ ℂ`, the ring of the entries of the Clifford operators (§2.1). -/
def ZThirdOmega : Subring ℂ := Subring.closure {(3 : ℂ)⁻¹, ωℂ}

theorem star_ωℂ : star ωℂ = ωℂ ^ 2 := by
  rw [ωℂ_eq, star_sub, star_pow, star_ζ, star_one]
  linear_combination (ζ ^ 2 - 2) * ζ_pow_four

theorem starClosed_ZThirdOmega : StarClosed ZThirdOmega := by
  apply starClosed_closure
  rintro x (rfl | rfl)
  · rw [star_inv₀, star_ofNat]; exact Subring.subset_closure (by simp)
  · rw [star_ωℂ]
    exact pow_mem (Subring.subset_closure (by simp) : ωℂ ∈ Subring.closure {(3 : ℂ)⁻¹, ωℂ}) 2

theorem pauliGroup_finite (n : ℕ) : (pauliGroup n).Finite := Set.finite_range _

theorem conj_injective {n : ℕ} (U : unitaryGroup (State 3 n) ℂ) :
    Function.Injective fun P : Op ℂ 3 n => (U : Op ℂ 3 n) * P * star (U : Op ℂ 3 n) := by
  intro P P' h
  have hU : star (U : Op ℂ 3 n) * U = 1 := (mem_unitaryGroup_iff'.1 U.2)
  have := congrArg (fun M => star (U : Op ℂ 3 n) * M * U) h
  simp only [← mul_assoc, hU, one_mul] at this
  simpa [mul_assoc, hU] using this

/-- The `n`-qutrit Clifford group `𝒞ₙ` (Definition 2.3): the unitaries `U`
with `U P U† ∈ 𝒫ₙ` for every `P ∈ 𝒫ₙ`, restricted, as in §2.1, to the
matrices with entries in `ℤ[1/3, ωℂ]`. -/
def cliffordGroup (n : ℕ) : Subgroup (unitaryGroup (State 3 n) ℂ) where
  carrier := {U | (∀ s t, (U : Op ℂ 3 n) s t ∈ ZThirdOmega) ∧
    ∀ P ∈ pauliGroup n, (U : Op ℂ 3 n) * P * star (U : Op ℂ 3 n) ∈ pauliGroup n}
  one_mem' := ⟨fun s t => by
      show (1 : Op ℂ 3 n) s t ∈ ZThirdOmega
      rw [one_apply]; split_ifs
      · exact ZThirdOmega.one_mem
      · exact ZThirdOmega.zero_mem,
    fun P hP => by simpa using hP⟩
  mul_mem' := by
    rintro U V ⟨hU, hU'⟩ ⟨hV, hV'⟩
    refine ⟨fun s t => ?_, fun P hP => ?_⟩
    · show ((U : Op ℂ 3 n) * V) s t ∈ ZThirdOmega
      rw [mul_apply]
      exact Subring.sum_mem _ fun u _ => Subring.mul_mem _ (hU s u) (hV u t)
    · have := hU' _ (hV' P hP)
      simp only [Submonoid.coe_mul, star_mul, ← mul_assoc] at this ⊢
      exact this
  inv_mem' := by
    rintro U ⟨hU, hU'⟩
    have hstar : ((U⁻¹ : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) = star (U : Op ℂ 3 n) := rfl
    refine ⟨fun s t => ?_, fun P hP => ?_⟩
    · rw [hstar, star_eq_conjTranspose, conjTranspose_apply]
      exact starClosed_ZThirdOmega _ (hU t s)
    · -- conjugation by `U` permutes the finite set `𝒫ₙ`
      have hbij := ((pauliGroup_finite n).injOn_iff_bijOn_of_mapsTo
        (f := fun P : Op ℂ 3 n => (U : Op ℂ 3 n) * P * star (U : Op ℂ 3 n))
        (fun P hP => hU' P hP)).1 (conj_injective U).injOn
      obtain ⟨P', hP', hPP'⟩ := hbij.surjOn hP
      have hU1 : star (U : Op ℂ 3 n) * U = 1 := mem_unitaryGroup_iff'.1 U.2
      rw [hstar, star_star, ← hPP']
      simp only [← mul_assoc, hU1, one_mul]
      simpa [mul_assoc, hU1] using hP'

end

end QCert.QutritClifford
