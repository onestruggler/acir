/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qudit Clifford circuits: soundness

Each rule of Figure 1 is sound for the matrices of Definition 2.11, at
every odd prime `p` (Proposition A.28, by the path-sum calculations of
Lemmas A.25–A.27).  Proved here: the rules whose
circuits are diagonal, (C0), (C1), (C6) and (C8); the others are in
`QuditClifford.Theorem` (`rule_sound`), with `sorry`s that `README.md`
lists.
-/
import QCert.QuditClifford.Semantics

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Diagonal operators -/

omit hp in
theorem onBottom_zero_one (A : Op ℂ p 1) : onBottom (n := 0) A = A := by
  ext s t; rw [onBottom_apply', if_pos (fun i hi hk => by omega)]

omit hp in
theorem onBottom_zero_two (A : Op ℂ p 2) : onBottom (n := 0) A = A := by
  ext s t; rw [onBottom_apply', if_pos (fun i hi hk => by omega)]

omit hp in
theorem onTop_diagonal {n k : ℕ} (d : State p n → ℂ) :
    onTop k (Matrix.diagonal d) = Matrix.diagonal fun s => d (split p n k s).2 := by
  ext s t
  rw [onTop_apply, diagonal_apply, diagonal_apply]
  by_cases h : s = t
  · subst h; simp
  · rw [if_neg h]
    split_ifs with h1 h2
    · exact absurd ((split p n k).injective (Prod.ext h1 h2)) h
    · rfl
    · rfl

theorem sem_S : ((sem p 1 S : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) = Sop p := by
  show onBottom (n := 0) (Sop p) = Sop p
  exact onBottom_zero_one p _

theorem sem_CZ : ((sem p 2 CZ : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) = CZop p := by
  show onBottom (n := 0) (CZop p) = CZop p
  exact onBottom_zero_two p _

theorem sem_negω {n : ℕ} :
    ((sem p n negω : unitaryGroup (State p n) ℂ) : Op ℂ p n) = Matrix.diagonal fun _ => -ωℂ p := by
  show (-ωℂ p) • (1 : Op ℂ p n) = _
  ext s t; by_cases h : s = t <;> simp [h]

theorem diagonal_pow_eq_one {m : Type} [Fintype m] [DecidableEq m] (e : m → ℕ) :
    (Matrix.diagonal fun s => ωℂ p ^ e s) ^ p = 1 := by
  rw [diagonal_pow, ← diagonal_one]
  congr 1; funext s
  rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, ωℂ_pow_p, one_pow]

/-! ### The diagonal rules -/

/-- (C0) `(-ω)^{2p} = 1`. -/
theorem sound_C0 : sem p 0 (negω ^ (2 * p)) = sem p 0 1 := by
  apply Subtype.ext
  rw [map_pow, SubmonoidClass.coe_pow, sem_negω, map_one, Submonoid.coe_one, diagonal_pow,
    ← diagonal_one]
  congr 1; funext s
  rw [Pi.pow_apply, pow_mul, neg_sq, ← pow_mul, mul_comm, pow_mul, ωℂ_pow_p, one_pow]

/-- (C1) `S^p = 1`. -/
theorem sound_C1 : sem p 1 (S ^ p) = sem p 1 1 := by
  apply Subtype.ext
  rw [map_pow, SubmonoidClass.coe_pow, sem_S, map_one, Submonoid.coe_one]
  exact diagonal_pow_eq_one p _

/-- (C6) `CZ^p = 1`. -/
theorem sound_C6 : sem p 2 (CZ ^ p) = sem p 2 1 := by
  apply Subtype.ext
  rw [map_pow, SubmonoidClass.coe_pow, sem_CZ, map_one, Submonoid.coe_one]
  exact diagonal_pow_eq_one p _

/-- (C8) `S` on the top wire commutes with `CZ`. -/
theorem sound_C8 : sem p 2 (top S ⨾ CZ) = sem p 2 (CZ ⨾ top S) := by
  apply Subtype.ext
  have hS : ((sem p 2 (top S) : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) = onTop 1 (Sop p) := by
    have := (gateSem p).sem_shift (n := 1) S
    rw [this]; show onTop 1 _ = _; rw [sem_S]
  rw [seq_def, seq_def, map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, hS, sem_CZ, Sop,
    onTop_diagonal, CZop, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext s; ring

end QCert.QuditClifford
