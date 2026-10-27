/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The Gray code, `toP`, and products of disjoint pair matrices

Support for the proof that the encoding of Definition 8.2 preserves the
semantics (`ESemProof`).

* The Gray code is a bijection of `{0, …, 2ⁿ - 1}` (`gray_gInv`,
  `gInv_gray`), so `toP` is conjugation by a permutation and respects
  products (`toP_mul`).
* `clr p s` is `s` with its bit on wire `p` cleared, `bit p s` that bit.  A
  matrix `E u` acting on the pair of indices `G⁻¹(u), G⁻¹(u + 2^p)` (`u`
  with bit `p` cleared), as the identity elsewhere: a product of such
  matrices over a list of distinct `u` acts on each pair as its own factor
  and as the identity off the pairs (`prod_pairs`).
* The two kinds of factors of the encoding: `H_[G⁻¹(u), G⁻¹(u + 2^p)]`
  (`hM_pair`) and `(-1)_[G⁻¹(u + 2^p)]` (`negM_pair`).
-/
import QCert.RealCliffordCH.Sec8.Encoding

namespace QCert.RealCliffordCH.Sec8

open Matrix

/-! ## The Gray code -/

theorem gInv_succ (n s : ℕ) : gInv (n + 1) s = gInv n s ^^^ (s >>> n) := by
  simp [gInv, List.range_succ, List.foldl_append]

theorem testBit_gInv_high (n s b : ℕ) (hs : ∀ j, b ≤ j → s.testBit j = false) :
    (gInv n s).testBit b = false := by
  induction n with
  | zero => simp [gInv]
  | succ n ih =>
    rw [gInv_succ, Nat.testBit_xor, Nat.testBit_shiftRight, ih, hs _ (by omega)]; rfl

theorem testBit_gInv_tele (n s b : ℕ) :
    ((gInv n s).testBit b ^^ (gInv n s).testBit (b + 1)) = (s.testBit b ^^ s.testBit (b + n)) := by
  induction n with
  | zero => simp [gInv]
  | succ n ih =>
    rw [gInv_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight]
    have e : n + (b + 1) = b + (n + 1) := by omega
    rw [e, Nat.add_comm n b]
    revert ih
    cases (gInv n s).testBit b <;> cases (gInv n s).testBit (b + 1) <;>
      cases s.testBit b <;> cases s.testBit (b + n) <;> cases s.testBit (b + (n + 1)) <;> simp

theorem testBit_gray (k b : ℕ) : (gray k).testBit b = (k.testBit b ^^ k.testBit (b + 1)) := by
  rw [gray, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.add_comm 1 b]

theorem testBit_gInv_gray (n k b : ℕ) :
    (gInv n (gray k)).testBit b = (k.testBit b ^^ k.testBit (b + n)) := by
  induction n with
  | zero => simp [gInv]
  | succ n ih =>
    rw [gInv_succ, Nat.testBit_xor, Nat.testBit_shiftRight, ih, testBit_gray]
    rw [Nat.add_comm n b, show b + n + 1 = b + (n + 1) by omega]
    cases k.testBit b <;> cases k.testBit (b + n) <;> cases k.testBit (b + (n + 1)) <;> simp

theorem testBit_of_lt {s n j : ℕ} (hs : s < 2 ^ n) (hj : n ≤ j) : s.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) hj))

theorem gInv_lt {n s : ℕ} (hs : s < 2 ^ n) : gInv n s < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun j hj =>
    testBit_gInv_high n s j fun _ hi => testBit_of_lt hs (by omega)

theorem gray_lt {n k : ℕ} (hk : k < 2 ^ n) : gray k < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun j hj => by
    rw [testBit_gray, testBit_of_lt hk hj, testBit_of_lt hk (by omega)]; rfl

theorem gray_gInv {n s : ℕ} (hs : s < 2 ^ n) : gray (gInv n s) = s :=
  Nat.eq_of_testBit_eq fun b => by
    rw [testBit_gray, testBit_gInv_tele, testBit_of_lt hs (by omega : n ≤ b + n)]; simp

theorem gInv_gray {n k : ℕ} (hk : k < 2 ^ n) : gInv n (gray k) = k :=
  Nat.eq_of_testBit_eq fun b => by
    rw [testBit_gInv_gray, testBit_of_lt hk (by omega : n ≤ b + n)]; simp

theorem gx_val {n s : ℕ} (hs : s < 2 ^ n) : (gx n s : ℕ) = gInv n s := by
  simp [gx, ix, Nat.mod_eq_of_lt (gInv_lt hs)]

theorem gray_gx {n s : ℕ} (hs : s < 2 ^ n) : gray (gx n s) = s := by
  rw [gx_val hs, gray_gInv hs]

theorem gx_gray {n : ℕ} (i : Fin (2 ^ n)) : gx n (gray i) = i := by
  ext; rw [gx_val (gray_lt i.2), gInv_gray i.2]

theorem gx_inj {n s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) (h : gx n s = gx n t) : s = t := by
  rw [← gray_gx hs, ← gray_gx ht, h]

theorem gx_eq_iff {n s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) : gx n s = gx n t ↔ s = t :=
  ⟨gx_inj hs ht, fun h => h ▸ rfl⟩

/-- The Gray code as a permutation of the indices. -/
def grayPerm (n : ℕ) : Fin (2 ^ n) ≃ Fin (2 ^ n) where
  toFun i := ix n (gray i)
  invFun s := gx n s
  left_inv i := by
    show gx n (ix n (gray i) : ℕ) = i
    simp only [ix, Nat.mod_eq_of_lt (gray_lt i.2)]; exact gx_gray i
  right_inv s := by
    ext; simp only [ix]; rw [gray_gx s.2, Nat.mod_eq_of_lt s.2]

/-- The basis ordered by the Gray code. -/
def grayEquiv (n : ℕ) : Fin (2 ^ n) ≃ State 2 n := (grayPerm n).trans finFunctionFinEquiv.symm

theorem toP_eq {R : Type*} {n : ℕ} (M : Op R 2 n) :
    toP M = M.submatrix (grayEquiv n) (grayEquiv n) := rfl

theorem toP_mul {R : Type*} [CommRing R] {n : ℕ} (M N : Op R 2 n) :
    toP (M * N) = toP M * toP N := by
  simp only [toP_eq, submatrix_mul_equiv]

theorem toP_one {R : Type*} [CommRing R] {n : ℕ} : toP (1 : Op R 2 n) = 1 := by
  rw [toP_eq, submatrix_one_equiv]

theorem toP_gx {R : Type*} {n s t : ℕ} (M : Op R 2 n) (hs : s < 2 ^ n) (ht : t < 2 ^ n) :
    toP M (gx n s) (gx n t) = M (stateOf n s) (stateOf n t) := by
  simp only [toP, grayState, gray_gx hs, gray_gx ht]

/-- Two matrices on the indices agree when they agree at every pair of
indices `G⁻¹(s), G⁻¹(t)`. -/
theorem ext_gx {R : Type*} {n : ℕ} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R}
    (h : ∀ s < 2 ^ n, ∀ t < 2 ^ n, A (gx n s) (gx n t) = B (gx n s) (gx n t)) : A = B := by
  ext i j
  have := h _ (gray_lt i.2) _ (gray_lt j.2)
  rwa [gx_gray, gx_gray] at this

/-! ## Bits -/

/-- The bit of `s` on wire `p`. -/
def bit (p s : ℕ) : ℕ := s / 2 ^ p % 2

/-- `s` with its bit on wire `p` cleared. -/
def clr (p s : ℕ) : ℕ := s % 2 ^ p + s / 2 ^ (p + 1) * 2 ^ (p + 1)

theorem bit_lt (p s : ℕ) : bit p s < 2 := Nat.mod_lt _ (by norm_num)

/-- Dividing `X * P + y` by `P`, `y < P`. -/
theorem div_mod_mul_add {P : ℕ} (X : ℕ) {y : ℕ} (hy : y < P) :
    (X * P + y) / P = X ∧ (X * P + y) % P = y := by
  have hP : 0 < P := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hy, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

theorem div_two_pow_add (s ℓ j : ℕ) : s / 2 ^ (ℓ + j) = s / 2 ^ ℓ / 2 ^ j := by
  rw [Nat.div_div_eq_div_mul, pow_add]

/-- The bit on wire `ℓ + j` of `X * 2^ℓ + y`, `y < 2^ℓ`. -/
theorem bit_mul_add (ℓ j X : ℕ) {y : ℕ} (hy : y < 2 ^ ℓ) :
    bit (ℓ + j) (X * 2 ^ ℓ + y) = X / 2 ^ j % 2 := by
  rw [bit, div_two_pow_add, (div_mod_mul_add X hy).1]

theorem bit_mul_add₀ (ℓ X : ℕ) {y : ℕ} (hy : y < 2 ^ ℓ) : bit ℓ (X * 2 ^ ℓ + y) = X % 2 := by
  rw [bit, (div_mod_mul_add X hy).1]

theorem clr_add_bit (p s : ℕ) : clr p s + bit p s * 2 ^ p = s := by
  unfold clr bit
  have h1 := Nat.div_add_mod s (2 ^ p)
  have h2 := Nat.div_add_mod (s / 2 ^ p) 2
  rw [Nat.div_div_eq_div_mul, ← pow_succ] at h2
  have e : s / 2 ^ (p + 1) * 2 ^ (p + 1) = 2 ^ p * (2 * (s / 2 ^ (p + 1))) := by ring
  rw [e]
  rw [← h2, mul_add] at h1
  linarith

/-- `s` is `Q * 2^p + r`, `r < 2^p`, with `Q = s / 2^p`. -/
theorem clr_eq (p s : ℕ) : clr p s = (s / 2 ^ p / 2 * 2) * 2 ^ p + s % 2 ^ p := by
  unfold clr
  rw [Nat.add_comm, div_two_pow_add s p 1, pow_one, pow_succ]; ring

theorem bit_clr (p s : ℕ) : bit p (clr p s) = 0 := by
  rw [clr_eq, bit_mul_add₀ _ _ (Nat.mod_lt _ (Nat.two_pow_pos p))]
  simp

theorem clr_mod (p s : ℕ) : clr p s % 2 ^ p = s % 2 ^ p := by
  unfold clr
  rw [show s / 2 ^ (p + 1) * 2 ^ (p + 1) = 2 ^ p * (s / 2 ^ (p + 1) * 2) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_mod]

theorem clr_div (p s : ℕ) : clr p s / 2 ^ (p + 1) = s / 2 ^ (p + 1) := by
  unfold clr
  have : s % 2 ^ p < 2 ^ (p + 1) :=
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos p)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.add_comm, (div_mod_mul_add _ this).1]

theorem clr_eq_iff (p s t : ℕ) :
    clr p s = clr p t ↔ s % 2 ^ p = t % 2 ^ p ∧ s / 2 ^ (p + 1) = t / 2 ^ (p + 1) := by
  constructor
  · intro h; rw [← clr_mod, h, clr_mod, ← clr_div, h, clr_div]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; unfold clr; rw [h1, h2]

theorem bit_of_lt_mod {q p : ℕ} (h : q < p) (s : ℕ) : bit q s = bit q (s % 2 ^ p) := by
  unfold bit
  rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, Nat.testBit_mod_two_pow]
  simp [h]

theorem bit_of_gt_div {q p : ℕ} (h : p < q) (s : ℕ) :
    bit q s = s / 2 ^ (p + 1) / 2 ^ (q - (p + 1)) % 2 := by
  unfold bit; rw [← div_two_pow_add]; congr 3; omega

theorem bit_clr_ne (p q s : ℕ) (h : q ≠ p) : bit q (clr p s) = bit q s := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · rw [bit_of_lt_mod h, clr_mod, ← bit_of_lt_mod h]
  · rw [bit_of_gt_div h, clr_div, ← bit_of_gt_div h]

theorem clr_of_bit {p u : ℕ} (h : bit p u = 0) : clr p u = u := by
  have := clr_add_bit p u; rw [h] at this; omega

theorem clr_clr (p s : ℕ) : clr p (clr p s) = clr p s := clr_of_bit (bit_clr p s)

theorem clr_le (p s : ℕ) : clr p s ≤ s := by
  have := clr_add_bit p s; omega

theorem bit_add_pow {p u : ℕ} (h : bit p u = 0) : bit p (u + 2 ^ p) = 1 ∧ clr p (u + 2 ^ p) = u := by
  have hr := Nat.mod_lt u (Nat.two_pow_pos p)
  have hd := Nat.div_add_mod u (2 ^ p)
  have e : u + 2 ^ p = (u / 2 ^ p + 1) * 2 ^ p + u % 2 ^ p := by
    rw [add_mul, one_mul]; linarith
  have hQ : u / 2 ^ p % 2 = 0 := h
  constructor
  · rw [e, bit_mul_add₀ _ _ hr]; omega
  · rw [clr_eq, e, (div_mod_mul_add _ hr).1, (div_mod_mul_add _ hr).2,
      show (u / 2 ^ p + 1) / 2 * 2 = u / 2 ^ p by omega]
    linarith

end QCert.RealCliffordCH.Sec8
