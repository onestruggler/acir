/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The encoding of a gate preserves its semantics

For a generator `g` of `n`-wire circuits, the encoding `encAt n 0 g`
(Definition 8.2) is a proper word whose matrix is the operator of `g` in
the basis ordered by the Gray code (`encAt_sem`).  By induction on the
generator: a generator moved up one wire has one more wire below it
(`ℓ + 1`), and the eight cases of a gate (`H`, `Z`, `CZ`, `CH`, with or
without wires below) are words of pair letters over one of the four shapes
of `Shapes`.
-/
import QCert.RealCliffordCH.Sec8.ESem.Shapes

namespace QCert.RealCliffordCH.Sec8

open Matrix

/-! ## Basis states as numbers -/

theorem stateOf_val (n v : ℕ) (i : Fin n) : (stateOf n v i : ℕ) = v % 2 ^ n / 2 ^ (i : ℕ) % 2 := by
  simp [stateOf, ix, finFunctionFinEquiv_symm_apply_val]

theorem stateOf_eq_iff (k v w : ℕ) : stateOf k v = stateOf k w ↔ v % 2 ^ k = w % 2 ^ k := by
  simp [stateOf, ix, Fin.ext_iff]

theorem split_stateOf (m k v : ℕ) :
    split 2 m k (stateOf (m + k) v) = (stateOf k v, stateOf m (v / 2 ^ k)) := by
  ext i
  · simp only [split, Equiv.coe_fn_mk, stateOf_val]
    rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow]
    have : (i : ℕ) < k := i.2
    simp [this, show (i : ℕ) < m + k by omega]
  · simp only [split, Equiv.coe_fn_mk, stateOf_val]
    rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    have : (i : ℕ) < m := i.2
    simp [this, show k + (i : ℕ) < m + k by omega, Nat.add_comm k]

theorem ofMat_stateOf {R : Type*} {k : ℕ} (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R) (v w : ℕ) :
    ofMat M (stateOf k v) (stateOf k w) = M (ix k v) (ix k w) := by
  simp [ofMat, stateOf]

/-! ## The operators of the generators on numbers -/

theorem sem_up {m : ℕ} (g : Gen Gate m) (v w : ℕ) :
    (S.gen g.up).1 (stateOf (m + 1) v) (stateOf (m + 1) w) =
      if v % 2 = w % 2 then (S.gen g).1 (stateOf m (v / 2)) (stateOf m (w / 2)) else 0 := by
  show onTop 1 (S.gen g).1 _ _ = _
  rw [onTop_apply, split_stateOf, split_stateOf]
  simp only [stateOf_eq_iff, pow_one]

theorem sem_gate1 {m : ℕ} (G : Gate 1) {v w : ℕ} (hv : v < 2 ^ (m + 1)) (hw : w < 2 ^ (m + 1)) :
    (S.gen (Gen.gate1 (n := m) G)).1 (stateOf (m + 1) v) (stateOf (m + 1) w) =
      if v / 2 = w / 2 then (S.gate1 G).1 (stateOf 1 v) (stateOf 1 w) else 0 := by
  show onBottom (n := m) (S.gate1 G).1 _ _ = _
  rw [onBottom_apply, split_stateOf, split_stateOf]
  simp only [stateOf_eq_iff, pow_one]
  rw [Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rwa [← pow_succ]),
    Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rwa [← pow_succ])]

theorem sem_gate2 {m : ℕ} (G : Gate 2) {v w : ℕ} (hv : v < 2 ^ (m + 2)) (hw : w < 2 ^ (m + 2)) :
    (S.gen (Gen.gate2 (n := m) G)).1 (stateOf (m + 2) v) (stateOf (m + 2) w) =
      if v / 4 = w / 4 then (S.gate2 G).1 (stateOf 2 v) (stateOf 2 w) else 0 := by
  show onBottom (n := m) (S.gate2 G).1 _ _ = _
  rw [onBottom_apply, split_stateOf, split_stateOf]
  simp only [stateOf_eq_iff, show (2 : ℕ) ^ 2 = 4 by norm_num]
  have e : 2 ^ (m + 2) = 2 ^ m * 4 := by rw [pow_add]; norm_num
  rw [Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by norm_num), ← e]; exact hv),
    Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by norm_num), ← e]; exact hw)]

theorem ix_one (a : ℕ) : ix 1 a = (⟨a % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) :=
  Fin.ext (by simp [ix])

theorem ix_two (a : ℕ) : ix 2 a = (⟨a % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) :=
  Fin.ext (by simp [ix])

/-- A controlled gate on bits `2c + a`: `E` on `a` when the control `c` is `1`. -/
def ctrlEnt {R : Type*} [CommRing R] (E : ℕ → ℕ → R) (a b : ℕ) : R :=
  if a / 2 = b / 2 then (if a / 2 = 1 then E (a % 2) (b % 2) else if a % 2 = b % 2 then 1 else 0)
  else 0

theorem gate1_H (v w : ℕ) :
    (S.gate1 Gate.H).1 (stateOf 1 v) (stateOf 1 w) = hEnt invSqrt2 (v % 2) (w % 2) := by
  show ofMat (d := 2) (k := 1) matH _ _ = _
  rw [ofMat_stateOf, ix_one, ix_one]
  generalize Nat.mod_lt v (by norm_num : 2 > 0) = hv
  generalize Nat.mod_lt w (by norm_num : 2 > 0) = hw
  generalize v % 2 = x at *; generalize w % 2 = y at *
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp [matH, hEnt, Fin.mk_one]

theorem gate1_Z (v w : ℕ) :
    (S.gate1 Gate.Z).1 (stateOf 1 v) (stateOf 1 w) = zEnt (v % 2) (w % 2) := by
  show ofMat (d := 2) (k := 1) matZ _ _ = _
  rw [ofMat_stateOf, ix_one, ix_one]
  generalize Nat.mod_lt v (by norm_num : 2 > 0) = hv
  generalize Nat.mod_lt w (by norm_num : 2 > 0) = hw
  generalize v % 2 = x at *; generalize w % 2 = y at *
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp [matZ, zEnt, Fin.mk_one]

theorem fin4_cases {x : ℕ} (h : x < 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega

theorem gate2_CZ (v w : ℕ) :
    (S.gate2 Gate.CZ).1 (stateOf 2 v) (stateOf 2 w) = ctrlEnt zEnt (v % 4) (w % 4) := by
  show ofMat (d := 2) (k := 2) matCZ _ _ = _
  rw [ofMat_stateOf, ix_two, ix_two]
  generalize Nat.mod_lt v (by norm_num : 4 > 0) = hv
  generalize Nat.mod_lt w (by norm_num : 4 > 0) = hw
  generalize v % 4 = x at *; generalize w % 4 = y at *
  rcases fin4_cases hv with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases hw with rfl | rfl | rfl | rfl <;> rfl

theorem gate2_CH (v w : ℕ) :
    (S.gate2 Gate.CH).1 (stateOf 2 v) (stateOf 2 w) = ctrlEnt (hEnt invSqrt2) (v % 4) (w % 4) := by
  show ofMat (d := 2) (k := 2) matCH _ _ = _
  rw [ofMat_stateOf, ix_two, ix_two]
  generalize Nat.mod_lt v (by norm_num : 4 > 0) = hv
  generalize Nat.mod_lt w (by norm_num : 4 > 0) = hw
  generalize v % 4 = x at *; generalize w % 4 = y at *
  rcases fin4_cases hv with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases hw with rfl | rfl | rfl | rfl <;> simp [matCH, ctrlEnt, hEnt]

/-! ## Comparing the two sides -/

/-- `s` in terms of its low part `s % 2^p` and high part `s / 2^p`. -/
theorem eq_iff_parts (p s t : ℕ) : s = t ↔ s % 2 ^ p = t % 2 ^ p ∧ s / 2 ^ p = t / 2 ^ p := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rw [← Nat.div_add_mod s (2 ^ p), h1, h2, Nat.div_add_mod]

theorem clr_eq_iff' (p s t : ℕ) :
    clr p t = clr p s ↔ s % 2 ^ p = t % 2 ^ p ∧ s / 2 ^ p / 2 = t / 2 ^ p / 2 := by
  rw [clr_eq_iff, div_two_pow_add t p 1, div_two_pow_add s p 1, pow_one]
  exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

theorem cmp1 {R : Type*} [CommRing R] (E : ℕ → ℕ → R) (p s t : ℕ) :
    (if clr p t = clr p s then E (bit p s) (bit p t) else if s = t then 1 else 0) =
      if s % 2 ^ p = t % 2 ^ p then
        (if s / 2 ^ p / 2 = t / 2 ^ p / 2 then E (s / 2 ^ p % 2) (t / 2 ^ p % 2) else 0)
      else 0 := by
  simp only [clr_eq_iff', eq_iff_parts p s t, bit]
  generalize s % 2 ^ p = A; generalize t % 2 ^ p = B
  generalize s / 2 ^ p = X; generalize t / 2 ^ p = Y
  by_cases h1 : A = B <;> by_cases h2 : X / 2 = Y / 2 <;> simp [h1, h2] <;> omega

theorem cmp2 {R : Type*} [CommRing R] (E : ℕ → ℕ → R) (p s t : ℕ) (P : Prop) [Decidable P]
    (hP : P ↔ bit (p + 1) s = 1) :
    (if P ∧ clr p t = clr p s then E (bit p s) (bit p t) else if s = t then 1 else 0) =
      if s % 2 ^ p = t % 2 ^ p then
        (if s / 2 ^ p / 4 = t / 2 ^ p / 4 then ctrlEnt E (s / 2 ^ p % 4) (t / 2 ^ p % 4) else 0)
      else 0 := by
  simp only [clr_eq_iff', eq_iff_parts p s t, hP, bit, ctrlEnt, div_two_pow_add s p 1, pow_one]
  generalize s % 2 ^ p = A; generalize t % 2 ^ p = B
  generalize s / 2 ^ p = X; generalize t / 2 ^ p = Y
  simp only [show X % 4 / 2 = X / 2 % 2 by omega, show Y % 4 / 2 = Y / 2 % 2 by omega,
    show X % 4 % 2 = X % 2 by omega, show Y % 4 % 2 = Y % 2 by omega]
  split_ifs <;> first | rfl | (exfalso; omega)

end QCert.RealCliffordCH.Sec8
