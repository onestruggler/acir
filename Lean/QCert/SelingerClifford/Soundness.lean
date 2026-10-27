/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): soundness

Every relation of Figure 8 holds for the matrices of (1.1).  Each is decided
exactly on the wires it is drawn on by simulating both sides on every basis
vector (`Sim.check`) over ℤ[ω], with `H` replaced by `√2 H`, whose entries
are integers; a circuit with `h` Hadamard gates then has `√2^h` times its
matrix (`eval_scaled`), and both sides are compared at the same power of
`√2`.  The structural rules are sound for every gate set.
-/
import QCert.SelingerClifford.Semantics
import QCert.SelingerClifford.Sim
import QCert.SelingerClifford.ZOmega

namespace QCert.SelingerClifford

open Matrix

/-- `√2 H`. -/
def opsH : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ZOmega := !![1, 1; 1, -1]
/-- `S`. -/
def opsS : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ZOmega := !![1, 0; 0, ZOmega.I]
/-- `Z_c`. -/
def opsCZ : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ZOmega :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- The gates over ℤ[ω], with `√2 H` for `H`. -/
def ops : GateOps Gate ZOmega 2 where
  scalar
    | .ω => ZOmega.X
  gate1
    | .H => ofMat opsH
    | .S => ofMat opsS
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

/-- `√2` in `ℂ`. -/
noncomputable abbrev sqrt2C : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

theorem map_ofMat {k : ℕ} (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ZOmega) :
    (ofMat M).map ZOmega.toC = ofMat (M.map ZOmega.toC) := rfl

theorem ops_gen {n : ℕ} (g : Gen Gate n) :
    (ops.map ZOmega.toC).gen g = sqrt2C ^ hk g • S.toOps.gen g := by
  induction g with
  | gate0 c =>
    cases c
    show ZOmega.toC ZOmega.X • (1 : Op ℂ 2 _) = 1 • (ω • 1)
    rw [ZOmega.toC_X, one_smul]
  | gate1 c =>
    cases c
    · show onBottom ((ofMat opsH).map ZOmega.toC) = sqrt2C ^ 1 • onBottom (ofMat matH)
      rw [← onBottom_smul, map_ofMat]
      congr 1
      have h := sqrt2_ne_zero
      ext s t
      simp only [ofMat, submatrix_apply, smul_apply, Matrix.map_apply, matH, opsH, smul_eq_mul,
        pow_one]
      generalize finFunctionFinEquiv s = i
      generalize finFunctionFinEquiv t = j
      fin_cases i <;> fin_cases j <;> simp [h, -ZOmega.one_def, -ZOmega.zero_def, -ZOmega.neg_def]
    · show onBottom ((ofMat opsS).map ZOmega.toC) = sqrt2C ^ 0 • onBottom (ofMat matS)
      rw [pow_zero, one_smul, map_ofMat]
      congr 2
      ext i j; fin_cases i <;> fin_cases j <;> simp [matS, opsS, ZOmega.toC_I, -ZOmega.one_def, -ZOmega.zero_def]
  | gate2 c =>
    cases c
    show onBottom ((ofMat opsCZ).map ZOmega.toC) = sqrt2C ^ 0 • onBottom (ofMat matCZ)
    rw [pow_zero, one_smul, map_ofMat]
    congr 2
    ext i j; fin_cases i <;> fin_cases j <;> simp [matCZ, opsCZ, -ZOmega.one_def, -ZOmega.zero_def, -ZOmega.neg_def]
  | gate3 c => exact nomatch c
  | up g ih =>
    show onTop 1 ((ops.map ZOmega.toC).gen g) = _ • onTop 1 (S.toOps.gen g)
    rw [ih, onTop_smul]
    rfl

/-- A circuit over ℤ[ω], read in `ℂ`, is `√2^h` times its matrix, `h` its
number of Hadamard gates. -/
theorem eval_scaled {n : ℕ} (w : Circ n) :
    (ops.eval n w).map ZOmega.toC = sqrt2C ^ hw w • S.toOps.eval n w := by
  rw [← GateOps.eval_map]
  exact Sim.eval_weight S.toOps (ops.map ZOmega.toC) sqrt2C hk ops_gen w

/-- An identity decided by simulation over ℤ[ω] holds for the matrices. -/
theorem sem_eq_of_check {k : ℕ} {w v : Circ k}
    (h : Sim.check ops (ZOmega.sqrt2 ^ hw v) (ZOmega.sqrt2 ^ hw w) w v = true) :
    S.sem k w = S.sem k v := by
  have e := congrArg (Matrix.map · ZOmega.toC) (Sim.eval_eq_of_check ops h)
  have hm : ∀ (a : ZOmega) (M : Op ZOmega 2 k),
      (a • M).map ZOmega.toC = ZOmega.toC a • M.map ZOmega.toC := fun a M => by
    ext s t; simp only [Matrix.map_apply, smul_apply, smul_eq_mul, map_mul]
  simp only at e
  rw [hm, hm, eval_scaled, eval_scaled, map_pow, map_pow, ZOmega.toC_sqrt2, smul_smul,
    smul_smul, ← pow_add, ← pow_add, add_comm (hw w)] at e
  apply Subtype.ext
  rw [GateSem.sem_val, GateSem.sem_val]
  exact smul_right_injective _ (pow_ne_zero _ sqrt2_ne_zero) e

/-- The relations of Figure 8 are sound. -/
theorem rel_sound : ∀ k w v, Rel k w v → S.sem k w = S.sem k v := by
  intro k w v h
  apply sem_eq_of_check
  cases h <;> decide +kernel

/-- Every rule of the theory, structural or not, is sound. -/
theorem theory_sound : ∀ n w v, Theory n w v → S.sem n w = S.sem n v :=
  S.lift_sound (S.padded_sound rel_sound)

end QCert.SelingerClifford
