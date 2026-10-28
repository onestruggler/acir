/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E: the patterns of Equations (36) and (37)

When `G(a), G(b), G(c), G(d)` are `x0y0z, x1y0z, x0y1z, x1y1z` (the two
distinguished bits on the wires `u > w`), `patt` finds the form `1` at
`(u, w)` (`patt_one`); for `x0y0z, x0y1z, x1y0z, x1y1z`, the form `2`
(`patt_two`).  Any other pair of wires leaves two of the four states
different after clearing its bits.
-/
import QCert.RealCliffordCH.Sec8.E.Lemma87Gates

namespace QCert.RealCliffordCH.Sec8.E

theorem sub_two_pow_eq_xor {v t : ℕ} (h : v.testBit t = true) : v - 2 ^ t = v ^^^ 2 ^ t := by
  have h' : (v ^^^ 2 ^ t).testBit t = false := by rw [Nat.testBit_xor, h, Nat.testBit_two_pow_self]; rfl
  have := add_two_pow_eq_xor h'
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
  omega

theorem testBit_clr1 (v t q : ℕ) :
    (v - bitOf v t * 2 ^ t).testBit q = (v.testBit q && !decide (q = t)) := by
  rw [bitOf_eq]
  cases hb : v.testBit t
  · simp only [Bool.toNat_false, Nat.zero_mul, Nat.sub_zero]
    by_cases hq : q = t
    · subst hq; simp [hb]
    · simp [hq]
  · simp only [Bool.toNat_true, Nat.one_mul]
    rw [sub_two_pow_eq_xor hb, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases hq : q = t
    · subst hq; simp [hb]
    · simp [hq, Ne.symm hq]

theorem testBit_clear2 (v u w q : ℕ) (huw : u ≠ w) :
    (clear2 v u w).testBit q = (v.testBit q && !decide (q = u) && !decide (q = w)) := by
  unfold clear2
  have e : bitOf v w = bitOf (v - bitOf v u * 2 ^ u) w := by
    rw [bitOf_eq_bitOf.2]; rw [testBit_clr1]; simp [Ne.symm huw]
  rw [e, testBit_clr1, testBit_clr1]

theorem clear2_ne {v v' u w x : ℕ} (huw : u ≠ w) (hx : x ≠ u ∧ x ≠ w)
    (h : v'.testBit x ≠ v.testBit x) : clear2 v u w ≠ clear2 v' u w := by
  intro e
  apply h
  have := congrArg (fun t => Nat.testBit t x) e
  simp only [testBit_clear2 _ _ _ _ huw, hx.1, hx.2, decide_false, Bool.not_false,
    Bool.and_true] at this
  exact this.symm

theorem testBit_xor_pow_self (s u : ℕ) : (s ^^^ 2 ^ u).testBit u = !s.testBit u := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self]; cases s.testBit u <;> rfl

theorem testBit_xor_pow_ne {s u q : ℕ} (h : q ≠ u) : (s ^^^ 2 ^ u).testBit q = s.testBit q := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm h)]; simp

/-- The body of `patt` at a pair of wires. -/
def pattAt (a b c d u w : ℕ) : Option (ℕ × ℕ × ℕ) :=
  let g := fun t => gray t
  let same := clear2 (g a) u w = clear2 (g b) u w ∧ clear2 (g a) u w = clear2 (g c) u w ∧
    clear2 (g a) u w = clear2 (g d) u w
  let bits := fun t => (bitOf (g t) u, bitOf (g t) w)
  if same ∧ bits a = (0, 0) ∧ bits b = (1, 0) ∧ bits c = (0, 1) ∧ bits d = (1, 1) then
    some (1, u, w)
  else if same ∧ bits a = (0, 0) ∧ bits b = (0, 1) ∧ bits c = (1, 0) ∧ bits d = (1, 1) then
    some (2, u, w)
  else none

theorem patt_eq (n a b c d : ℕ) :
    patt n a b c d = (List.range n).findSome? fun u => (List.range u).findSome? fun w =>
      pattAt a b c d u w := rfl

/-- Four states that differ in the bits `u0` and `w0`, in one of the two orders. -/
structure Four (a b c d s u0 w0 : ℕ) : Prop where
  ha : gray a = s
  hd : gray d = s ^^^ 2 ^ u0 ^^^ 2 ^ w0
  hbc : (gray b = s ^^^ 2 ^ u0 ∧ gray c = s ^^^ 2 ^ w0) ∨ (gray b = s ^^^ 2 ^ w0 ∧ gray c = s ^^^ 2 ^ u0)

theorem pattAt_none {a b c d s u0 w0 u w : ℕ} (hf : Four a b c d s u0 w0) (hw0 : w0 < u0)
    (hw : w < u) (hne : ¬ (u = u0 ∧ w = w0)) : pattAt a b c d u w = none := by
  have hns : ¬ (clear2 (gray a) u w = clear2 (gray b) u w ∧ clear2 (gray a) u w = clear2 (gray c) u w ∧
      clear2 (gray a) u w = clear2 (gray d) u w) := by
    rintro ⟨e1, e2, _⟩
    have huw : u ≠ w := by omega
    -- one of `u0`, `w0` is not among `u`, `w`
    have key : (u0 ≠ u ∧ u0 ≠ w) ∨ (w0 ≠ u ∧ w0 ≠ w) := by omega
    rcases hf.hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩ <;> rcases key with k | k
    · exact clear2_ne huw k (by rw [hb, hf.ha, testBit_xor_pow_self]; cases s.testBit u0 <;> simp) e1
    · exact clear2_ne huw k (by rw [hc, hf.ha, testBit_xor_pow_self]; cases s.testBit w0 <;> simp) e2
    · exact clear2_ne huw k (by rw [hc, hf.ha, testBit_xor_pow_self]; cases s.testBit u0 <;> simp) e2
    · exact clear2_ne huw k (by rw [hb, hf.ha, testBit_xor_pow_self]; cases s.testBit w0 <;> simp) e1
  unfold pattAt
  simp only
  rw [if_neg (fun h => hns h.1), if_neg (fun h => hns h.1)]

theorem findSome_range_at {β : Type*} (f : ℕ → Option β) (n x : ℕ) (hx : x < n) (r : β)
    (hnone : ∀ y < x, f y = none) (hsome : f x = some r) : (List.range n).findSome? f = some r := by
  rw [show n = x + (n - x) by omega, List.range_add, List.findSome?_append,
    show n - x = (n - x - 1) + 1 by omega, List.range_succ_eq_map]
  have h1 : (List.range x).findSome? f = none := by
    rw [List.findSome?_eq_none_iff]; intro y hy; exact hnone y (List.mem_range.1 hy)
  rw [h1]
  simp [hsome]

theorem patt_of_four {n a b c d s u0 w0 : ℕ} (hf : Four a b c d s u0 w0) (hw0 : w0 < u0)
    (hu0 : u0 < n) (r : ℕ × ℕ × ℕ) (hr : pattAt a b c d u0 w0 = some r) : patt n a b c d = some r := by
  rw [patt_eq]
  apply findSome_range_at _ n u0 hu0 r
  · intro y hy
    rw [List.findSome?_eq_none_iff]
    intro w hw
    exact pattAt_none hf hw0 (List.mem_range.1 hw) (by omega)
  · apply findSome_range_at _ u0 w0 hw0 r
    · intro y hy; exact pattAt_none hf hw0 (by omega) (by omega)
    · exact hr

theorem clear2_xor {s u w x : ℕ} (huw : u ≠ w) (hx : x = u ∨ x = w) :
    clear2 (s ^^^ 2 ^ x) u w = clear2 s u w := by
  apply Nat.eq_of_testBit_eq; intro q
  rw [testBit_clear2 _ _ _ _ huw, testBit_clear2 _ _ _ _ huw]
  by_cases hq : q = x
  · subst hq; rcases hx with rfl | rfl <;> simp [huw, Ne.symm huw]
  · rw [testBit_xor_pow_ne hq]

/-- The form `x0y0z, x1y0z, x0y1z, x1y1z`. -/
theorem patt_one {n a b c d s u w : ℕ} (hwu : w < u) (hun : u < n) (hsu : s.testBit u = false)
    (hsw : s.testBit w = false) (ha : gray a = s) (hb : gray b = s ^^^ 2 ^ u)
    (hc : gray c = s ^^^ 2 ^ w) (hd : gray d = s ^^^ 2 ^ u ^^^ 2 ^ w) :
    patt n a b c d = some (1, u, w) := by
  have hf : Four a b c d s u w := ⟨ha, hd, Or.inl ⟨hb, hc⟩⟩
  apply patt_of_four hf hwu hun
  have huw : u ≠ w := by omega
  unfold pattAt
  simp only [ha, hb, hc, hd, clear2_xor huw (Or.inl rfl), clear2_xor huw (Or.inr rfl), bitOf_eq,
    testBit_xor_pow_self, testBit_xor_pow_ne huw, testBit_xor_pow_ne (Ne.symm huw), hsu, hsw]
  rfl

/-- The form `x0y0z, x0y1z, x1y0z, x1y1z`. -/
theorem patt_two {n a b c d s u w : ℕ} (hwu : w < u) (hun : u < n) (hsu : s.testBit u = false)
    (hsw : s.testBit w = false) (ha : gray a = s) (hb : gray b = s ^^^ 2 ^ w)
    (hc : gray c = s ^^^ 2 ^ u) (hd : gray d = s ^^^ 2 ^ u ^^^ 2 ^ w) :
    patt n a b c d = some (2, u, w) := by
  have hf : Four a b c d s u w := ⟨ha, hd, Or.inr ⟨hb, hc⟩⟩
  apply patt_of_four hf hwu hun
  have huw : u ≠ w := by omega
  unfold pattAt
  simp only [ha, hb, hc, hd, clear2_xor huw (Or.inl rfl), clear2_xor huw (Or.inr rfl), bitOf_eq,
    testBit_xor_pow_self, testBit_xor_pow_ne huw, testBit_xor_pow_ne (Ne.symm huw), hsu, hsw]
  rfl

end QCert.RealCliffordCH.Sec8.E
