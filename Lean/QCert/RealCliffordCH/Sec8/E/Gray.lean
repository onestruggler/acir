/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E: properties of the Gray code

The facts about the Gray code (Definition 8.1) that the proofs of
Lemmas 8.4 and 8.5 (Appendices E.2, E.3) use, stated on bits (`testBit`).

* `succ_spec`: `a + 1` is `a` with its trailing ones and the next bit
  flipped; so `G(a + 1)` is `G(a)` with one bit flipped, the bit `β` after
  the trailing ones of `a` (`gray_succ`), and `tOf n a = β` (`tOf_eq`).
* Pairs `p`, `q = p xor (2^(t+1) - 1)` with bit `t` of `p` clear: `G(p)` and
  `G(q)` differ in bit `t` only (`gray_pair`), `p < q`, and either
  `q = p + 1` or `(p + 1, q - 1)` is again such a pair, `G(p + 1)` and
  `G(q - 1)` being `G(p)` and `G(q)` with the same bit `β < t` flipped
  (`pair_step`).  This is the induction of the proofs of Lemmas 8.4 and 8.5.
-/
import QCert.RealCliffordCH.Sec8.E.Letters
import QCert.RealCliffordCH.Sec8.ESem.Basic
import Mathlib.Data.Nat.Bitwise

namespace QCert.RealCliffordCH.Sec8.E

/-! ## Bits -/

theorem bitOf_eq (v i : ℕ) : bitOf v i = (v.testBit i).toNat := by
  rw [bitOf, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

theorem bitOf_eq_bitOf {u v i : ℕ} : bitOf u i = bitOf v i ↔ u.testBit i = v.testBit i := by
  rw [bitOf_eq, bitOf_eq]
  cases u.testBit i <;> cases v.testBit i <;> simp

theorem gray_xor (a b : ℕ) : gray (a ^^^ b) = gray a ^^^ gray b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_gray, Nat.testBit_xor]
  cases a.testBit i <;> cases a.testBit (i + 1) <;> cases b.testBit i <;>
    cases b.testBit (i + 1) <;> rfl

theorem gray_mask (t : ℕ) : gray (2 ^ (t + 1) - 1) = 2 ^ t := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_gray, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases h : i = t
  · subst h; simp
  · by_cases h' : i < t
    · simp [show i < t + 1 by omega, show i + 1 < t + 1 by omega, show t ≠ i by omega]
    · simp [show ¬ i < t + 1 by omega, show ¬ i + 1 < t + 1 by omega, show t ≠ i by omega]

/-- `β` is the number of trailing ones of `a`. -/
def IsOnes (a β : ℕ) : Prop := (∀ j < β, a.testBit j = true) ∧ a.testBit β = false

theorem IsOnes.unique {a β β' : ℕ} (h : IsOnes a β) (h' : IsOnes a β') : β = β' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have := h'.1 β hl; rw [h.2] at this; exact absurd this (by simp)
  · have := h.1 β' hl; rw [h'.2] at this; exact absurd this (by simp)

/-- `a + 1` flips the trailing ones of `a` and the bit after them. -/
theorem succ_spec (a : ℕ) :
    ∃ β, IsOnes a β ∧ ∀ i, (a + 1).testBit i = (a.testBit i ^^ decide (i ≤ β)) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.mod_two_eq_zero_or_one a with h | h
    · refine ⟨0, ⟨fun j hj => absurd hj (by omega), by simp [Nat.testBit_zero, h]⟩, ?_⟩
      intro i
      cases i with
      | zero => simp [Nat.testBit_zero, h, Nat.add_mod]
      | succ i =>
        rw [Nat.testBit_add_one, Nat.testBit_add_one, show (a + 1) / 2 = a / 2 by omega]
        simp
    · obtain ⟨β, ⟨hβ1, hβ2⟩, hs⟩ := ih (a / 2) (by omega)
      refine ⟨β + 1, ⟨fun j hj => ?_, ?_⟩, fun i => ?_⟩
      · cases j with
        | zero => simp [Nat.testBit_zero, h]
        | succ j => rw [Nat.testBit_add_one]; exact hβ1 j (by omega)
      · rw [Nat.testBit_add_one]; exact hβ2
      · cases i with
        | zero => simp [Nat.testBit_zero, h, Nat.add_mod]
        | succ i =>
          rw [Nat.testBit_add_one, Nat.testBit_add_one, show (a + 1) / 2 = a / 2 + 1 by omega, hs i]
          simp

/-- `G(a + 1)` is `G(a)` with the bit `β` flipped, `β` the number of trailing
ones of `a`. -/
theorem gray_succ {a β : ℕ} (h : IsOnes a β) (i : ℕ) :
    (gray (a + 1)).testBit i = ((gray a).testBit i ^^ decide (i = β)) := by
  obtain ⟨β', hβ', hs⟩ := succ_spec a
  obtain rfl := hβ'.unique h
  rw [testBit_gray, testBit_gray, hs, hs]
  by_cases h1 : i = β'
  · subst h1; simp
  · by_cases h2 : i < β'
    · simp [show i ≤ β' by omega, show i + 1 ≤ β' by omega, h1]
    · simp [show ¬ i ≤ β' by omega, show ¬ i + 1 ≤ β' by omega, h1]

theorem isOnes_lt {a β n : ℕ} (h : IsOnes a β) (ha : a + 1 < 2 ^ n) : β < n := by
  obtain ⟨β', hβ', hs⟩ := succ_spec a
  obtain rfl := hβ'.unique h
  by_contra hn
  have h1 : (a + 1).testBit β' = true := by rw [hs]; simp [h.2]
  rw [testBit_of_lt ha (by omega)] at h1
  exact absurd h1 (by simp)

/-- The wire where `G(a)` and `G(a + 1)` differ is the number of trailing ones
of `a`. -/
theorem tOf_eq {n a β : ℕ} (h : IsOnes a β) (ha : a + 1 < 2 ^ n) : tOf n a = β := by
  have hβ := isOnes_lt h ha
  have hp : ∀ j, (bitOf (gray a) j ≠ bitOf (gray (a + 1)) j) ↔ j = β := by
    intro j
    rw [Ne, bitOf_eq_bitOf, gray_succ h]
    by_cases hj : j = β <;> simp [hj]
  unfold tOf
  rw [show n = β + (n - β) by omega, List.range_add, List.find?_append,
    show n - β = (n - β - 1) + 1 by omega, List.range_succ_eq_map]
  have hnone : (List.range β).find? (fun j => decide (bitOf (gray a) j ≠ bitOf (gray (a + 1)) j)) =
      none := by
    rw [List.find?_eq_none]
    intro j hj
    have := (hp j).not.2 (by simp at hj; omega)
    simpa using this
  rw [hnone]
  simp [(hp β).2 rfl]

/-! ## Pairs `G⁻¹(x0y)`, `G⁻¹(x1y)` -/

/-- The mask of the bits `0, …, t`. -/
abbrev msk (t : ℕ) : ℕ := 2 ^ (t + 1) - 1

theorem testBit_msk (t i : ℕ) : (msk t).testBit i = decide (i ≤ t) := by
  rw [Nat.testBit_two_pow_sub_one]; simp

/-- `G(p)` and `G(p xor (2^(t+1) - 1))` differ exactly in the bit `t`. -/
theorem gray_pair (p t : ℕ) : gray (p ^^^ msk t) = gray p ^^^ 2 ^ t := by
  rw [gray_xor, gray_mask]

/-- With the bit `t` of `p` clear, `p < p xor (2^(t+1) - 1)`. -/
theorem pair_lt {p t : ℕ} (hp : p.testBit t = false) : p < p ^^^ msk t := by
  apply Nat.lt_of_testBit t hp
  · rw [Nat.testBit_xor, testBit_msk, hp]; simp
  · intro j hj
    rw [Nat.testBit_xor, testBit_msk]; simp [show ¬ j ≤ t by omega]

/-- The two cases of the induction of Lemmas 8.4 and 8.5. -/
theorem pair_step {p t : ℕ} (hp : p.testBit t = false) :
    (IsOnes p t ∧ p ^^^ msk t = p + 1) ∨
    ∃ β, β < t ∧ IsOnes p β ∧ (p + 1).testBit t = false ∧
      IsOnes ((p + 1) ^^^ msk t) β ∧ p ^^^ msk t = ((p + 1) ^^^ msk t) + 1 := by
  obtain ⟨β, hβ, hs⟩ := succ_spec p
  rcases Nat.lt_or_ge β t with hlt | hge
  · right
    refine ⟨β, hlt, hβ, ?_, ⟨fun j hj => ?_, ?_⟩, ?_⟩
    · rw [hs, hp]; simp [show ¬ t ≤ β by omega]
    · rw [Nat.testBit_xor, hs, testBit_msk, hβ.1 j hj]; simp [show j ≤ β by omega, show j ≤ t by omega]
    · rw [Nat.testBit_xor, hs, testBit_msk, hβ.2]; simp [show β ≤ t by omega]
    · obtain ⟨β', hβ', hs'⟩ := succ_spec ((p + 1) ^^^ msk t)
      have hβ'' : IsOnes ((p + 1) ^^^ msk t) β := by
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [Nat.testBit_xor, hs, testBit_msk, hβ.1 j hj]
          simp [show j ≤ β by omega, show j ≤ t by omega]
        · rw [Nat.testBit_xor, hs, testBit_msk, hβ.2]; simp [show β ≤ t by omega]
      obtain rfl := hβ'.unique hβ''
      apply Nat.eq_of_testBit_eq; intro i
      rw [hs', Nat.testBit_xor, Nat.testBit_xor, hs, testBit_msk]
      by_cases h1 : i ≤ β'
      · simp [h1, show i ≤ t by omega]
      · simp [h1]
  · left
    have hβt : β = t := by
      by_contra hne
      have := hβ.1 t (by omega); rw [hp] at this; exact absurd this (by simp)
    subst hβt
    refine ⟨hβ, ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    rw [hs, Nat.testBit_xor, testBit_msk]

end QCert.RealCliffordCH.Sec8.E
