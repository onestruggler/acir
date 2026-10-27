/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: soundness

Every relation of Figure 1 holds for the matrices of §2.  Each is decided
exactly on the wires it is drawn on by simulating both sides on every basis
vector (`Sim.check`) over `ℤ[√2]`, with `H` replaced by `√2 H`, whose
entries are integers; a circuit with `h` Hadamard gates then has `√2^h`
times its matrix (`eval_scaled`), and both sides are compared at the same
power of `√2`.  The structural rules are sound for every gate set.
-/
import QCert.RealStabilizer.Semantics
import QCert.SelingerClifford.Sim
import Mathlib.NumberTheory.Zsqrtd.Basic

namespace QCert.RealStabilizer

open Matrix

/-- `ℤ[√2]` inside `ℝ`. -/
noncomputable def toR : ℤ√2 →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 2, by rw [Real.mul_self_sqrt (by norm_num)]; norm_num⟩

theorem toR_apply (a : ℤ√2) : toR a = a.re + a.im * Real.sqrt 2 := rfl

/-- `√2 H`. -/
def opsH : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) (ℤ√2) := !![1, 1; 1, -1]
/-- `Z`. -/
def opsZ : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) (ℤ√2) := !![1, 0; 0, -1]
/-- `CZ`. -/
def opsCZ : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) (ℤ√2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- The gates over `ℤ[√2]`, with `√2 H` for `H`. -/
def ops : GateOps Gate (ℤ√2) 2 where
  scalar
    | .neg => -1
  gate1
    | .H => ofMat opsH
    | .Z => ofMat opsZ
  gate2
    | .CZ => ofMat opsCZ
  gate3 g := nomatch g

/-- The number of Hadamard gates of a generator. -/
def hk : {n : ℕ} → Gen Gate n → ℕ
  | _, .gate1 .H => 1
  | _, .up g => hk g
  | _, _ => 0

/-- The number of Hadamard gates of a circuit. -/
def hw {n : ℕ} (w : Circ n) : ℕ := ((FreeMonoid.toList w).map hk).sum

theorem map_ofMat {k : ℕ} (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) (ℤ√2)) :
    (ofMat M).map toR = ofMat (M.map toR) := rfl

theorem sqrt2_ne_zero : Real.sqrt 2 ≠ 0 := by positivity

theorem ops_gen {n : ℕ} (g : Gen Gate n) :
    (ops.map toR).gen g = Real.sqrt 2 ^ hk g • S.toOps.gen g := by
  induction g with
  | gate0 c =>
    cases c
    show toR (-1) • (1 : Op ℝ 2 _) = 1 • ((-1 : ℝ) • 1)
    rw [map_neg, map_one, one_smul]
  | gate1 c =>
    cases c
    · show onBottom ((ofMat opsH).map toR) = Real.sqrt 2 ^ 1 • onBottom (ofMat matH)
      rw [← onBottom_smul, map_ofMat]
      congr 1
      have h := sqrt2_ne_zero
      ext s t
      simp only [ofMat, submatrix_apply, smul_apply, Matrix.map_apply, matH, opsH, smul_eq_mul,
        pow_one]
      generalize finFunctionFinEquiv s = i
      generalize finFunctionFinEquiv t = j
      fin_cases i <;> fin_cases j <;> simp [h]
    · show onBottom ((ofMat opsZ).map toR) = Real.sqrt 2 ^ 0 • onBottom (ofMat matZ)
      rw [pow_zero, one_smul, map_ofMat]
      congr 2
      ext i j; fin_cases i <;> fin_cases j <;> simp [matZ, opsZ]
  | gate2 c =>
    cases c
    show onBottom ((ofMat opsCZ).map toR) = Real.sqrt 2 ^ 0 • onBottom (ofMat matCZ)
    rw [pow_zero, one_smul, map_ofMat]
    congr 2
    ext i j; fin_cases i <;> fin_cases j <;> simp [matCZ, opsCZ]
  | gate3 c => exact nomatch c
  | up g ih =>
    show onTop 1 ((ops.map toR).gen g) = _ • onTop 1 (S.toOps.gen g)
    rw [ih, onTop_smul]
    rfl

/-- A circuit over `ℤ[√2]`, read in `ℝ`, is `√2^h` times its matrix, `h`
its number of Hadamard gates. -/
theorem eval_scaled {n : ℕ} (w : Circ n) :
    (ops.eval n w).map toR = Real.sqrt 2 ^ hw w • S.toOps.eval n w := by
  rw [← GateOps.eval_map]
  exact Sim.eval_weight S.toOps (ops.map toR) (Real.sqrt 2) hk ops_gen w

/-- `√2 ∈ ℤ[√2]`. -/
def sqrt2 : ℤ√2 := ⟨0, 1⟩

theorem toR_sqrt2 : toR sqrt2 = Real.sqrt 2 := by simp [toR_apply, sqrt2]

/-- An identity decided by simulation over `ℤ[√2]` holds for the matrices. -/
theorem sem_eq_of_check {k : ℕ} {w v : Circ k}
    (h : Sim.check ops (sqrt2 ^ hw v) (sqrt2 ^ hw w) w v = true) :
    S.sem k w = S.sem k v := by
  have e := congrArg (Matrix.map · toR) (Sim.eval_eq_of_check ops h)
  have hm : ∀ (a : ℤ√2) (M : Op (ℤ√2) 2 k), (a • M).map toR = toR a • M.map toR :=
    fun a M => by ext s t; simp only [Matrix.map_apply, smul_apply, smul_eq_mul, map_mul]
  simp only at e
  rw [hm, hm, eval_scaled, eval_scaled, map_pow, map_pow, toR_sqrt2, smul_smul,
    smul_smul, ← pow_add, ← pow_add, add_comm (hw w)] at e
  apply Subtype.ext
  rw [GateSem.sem_val, GateSem.sem_val]
  exact smul_right_injective _ (pow_ne_zero _ sqrt2_ne_zero) e

/-- The relations of Figure 1 are sound. -/
theorem rel_sound : ∀ k w v, Rel k w v → S.sem k w = S.sem k v := by
  intro k w v h
  apply sem_eq_of_check
  cases h <;> decide +kernel

/-- Every rule of the theory, structural or not, is sound. -/
theorem theory_sound : ∀ n w v, Theory n w v → S.sem n w = S.sem n v :=
  S.lift_sound (S.padded_sound rel_sound)

end QCert.RealStabilizer
