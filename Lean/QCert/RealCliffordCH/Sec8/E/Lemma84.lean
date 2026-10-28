/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.2: Lemma 8.4, by induction on `|G⁻¹(x0y) - G⁻¹(x1y)|`

`D((-1)_[G⁻¹(x0y)](-1)_[G⁻¹(x1y)])` is the box on the wire of the
distinguished bit, controlled by `x` and `y`.  The decoding of
`(-1)_[p](-1)_[q]`, `p < q`, is the product of the boxes `D((-1)_[k](-1)_[k+1])`,
`p ≤ k < q`; the first and the last are boxes on the same wire `β` (the bit
flipped by `p ↦ p + 1` and by `q - 1 ↦ q`), the middle is the statement for
`(p + 1, q - 1)` (`pair_step`).  The paper then rearranges the three boxes
with (307), (336), (309), (274) and (311); that step, at every pair of
wires, is `Step84`, and `lemma84_of` is the induction given it.
-/
import QCert.RealCliffordCH.Sec8.E.Gray
import QCert.RealCliffordCH.Sec8.E.Cheap

namespace QCert.RealCliffordCH.Sec8.E

open Circuit

/-- The box on wire `t` controlled by the bits of `s` on the other wires. -/
abbrev boxAt (n t s : ℕ) : Circ n := mc n .box [t] (ctlOf s t)

theorem ctlOf_flip (s t : ℕ) : ctlOf (s ^^^ 2 ^ t) t = ctlOf s t := by
  funext j
  unfold ctlOf
  split_ifs with h
  · rfl
  · congr 2
    rw [bitOf_eq_bitOf.2]
    rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm h)]; simp

/-- The step of the induction of Lemma 8.4 (Appendix E.2): with `s` the state
of `G(p)`, the boxes `D((-1)_[p](-1)_[p+1])` (on wire `β`), the box of the
induction hypothesis (on wire `t`, the bit `β` flipped) and
`D((-1)_[q-1](-1)_[q])` (on wire `β`, the bit `t` flipped) make the box on
wire `t`. -/
def Step84 (n : ℕ) : Prop :=
  ∀ β t s : ℕ, β < n → t < n → β ≠ t →
    Derivable (theory n) (drawn [boxAt n β s, boxAt n t (s ^^^ 2 ^ β), boxAt n β (s ^^^ 2 ^ t)])
      (boxAt n t s)

/-! ## `dZZ` unfolded -/

theorem dZZ_le {n a b : ℕ} (h : a ≤ b) :
    dZZ n a b = drawn ((List.range (b - a)).map fun i => dZZ1 n (a + i)) := by
  simp [dZZ, min_eq_left h, max_eq_right h]

theorem dZZ_comm (n a b : ℕ) : dZZ n a b = dZZ n b a := by
  simp only [dZZ, max_comm, min_comm]

theorem dZZ_succ (n a : ℕ) : dZZ n a (a + 1) = dZZ1 n a := by
  rw [dZZ_le (by omega)]; simp [drawn]

theorem drawn_append {n : ℕ} (l₁ l₂ : List (Circ n)) : drawn (l₁ ++ l₂) = drawn l₂ * drawn l₁ := by
  simp [drawn]

theorem drawn_single {n : ℕ} (x : Circ n) : drawn [x] = x := by simp [drawn]

theorem dZZ_split {n a b : ℕ} (h : a + 1 < b) :
    dZZ n a b = drawn [dZZ1 n a, dZZ n (a + 1) (b - 1), dZZ1 n (b - 1)] := by
  obtain ⟨m, rfl⟩ : ∃ m, b = a + m + 2 := ⟨b - a - 2, by omega⟩
  rw [dZZ_le (by omega), dZZ_le (by omega : a + 1 ≤ a + m + 2 - 1),
    show a + m + 2 - a = (m + 1) + 1 by omega, show a + m + 2 - 1 - (a + 1) = m by omega,
    List.range_succ, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_append, List.map_map, List.cons_append, List.map_nil]
  rw [show (dZZ1 n (a + 0) :: (List.map ((fun i => dZZ1 n (a + i)) ∘ Nat.succ) (List.range m) ++
      [dZZ1 n (a + (m + 1))])) = [dZZ1 n a] ++ (List.map (fun i => dZZ1 n (a + 1 + i))
      (List.range m)) ++ [dZZ1 n (a + m + 2 - 1)] by
    simp only [Nat.add_zero, List.singleton_append, List.cons_append, Function.comp_def,
      Nat.succ_eq_add_one, show a + m + 2 - 1 = a + (m + 1) by omega]
    congr 2
    apply List.map_congr_left; intro i _; congr 1; omega]
  rw [drawn_append, drawn_append]
  simp [drawn, mul_assoc]

/-! ## The induction -/

theorem gray_succ_eq {a β : ℕ} (h : IsOnes a β) : gray (a + 1) = gray a ^^^ 2 ^ β := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [gray_succ h, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : i = β
  · subst hi; simp
  · simp [hi, Ne.symm hi]

theorem ctlOf_xor_comm (s a b : ℕ) : s ^^^ a ^^^ b = s ^^^ b ^^^ a := by
  rw [Nat.xor_assoc, Nat.xor_comm a b, ← Nat.xor_assoc]

theorem testBit_pair_hi {p t : ℕ} (hp : p.testBit t = false) : (p ^^^ msk t).testBit t = true := by
  rw [Nat.testBit_xor, testBit_msk, hp]; simp

theorem lt_of_testBit_pow {q t n : ℕ} (hq : q.testBit t = true) (hn : q < 2 ^ n) : t < n := by
  by_contra h
  rw [testBit_of_lt hn (by omega)] at hq
  exact absurd hq (by simp)

/-- Lemma 8.4 given its step, for `p` with bit `t` clear and `q = p xor (2^(t+1) - 1)`:
`D((-1)_[p](-1)_[q])` is the box on wire `t` controlled by the other bits of `G(p)`. -/
theorem lemma84_of {k : ℕ} (hstep : Step84 (k + 1)) :
    ∀ (m p t : ℕ), (p ^^^ msk t) - p ≤ m → p.testBit t = false → p ^^^ msk t < 2 ^ (k + 1) →
      Derivable (theory (k + 1)) (dZZ (k + 1) p (p ^^^ msk t)) (boxAt (k + 1) t (gray p)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p t hm hp hq
  have ht : t < k + 1 := lt_of_testBit_pow (testBit_pair_hi hp) hq
  rcases pair_step hp with ⟨hon, he⟩ | ⟨β, hβt, hβ, hp1, hq1, he⟩
  · rw [he, dZZ_succ, dZZ1_mc, tOf_eq hon (by omega)]
  · set q' := (p + 1) ^^^ msk t with hq'
    have hlt : p + 1 < q' := pair_lt hp1
    rw [he, dZZ_split (by omega), Nat.add_sub_cancel]
    have hm' : q' - (p + 1) < m := by rw [he] at hm; omega
    have ih' := ih (q' - (p + 1)) hm' (p + 1) t le_rfl hp1 (by rw [he] at hq; omega)
    have hq2 : q' + 1 < 2 ^ (k + 1) := by rw [he] at hq; omega
    rw [dZZ1_mc, dZZ1_mc, tOf_eq hβ (by omega), tOf_eq hq1 hq2]
    have hg1 : gray (p + 1) = gray p ^^^ 2 ^ β := gray_succ_eq hβ
    have hg2 : gray q' = gray p ^^^ 2 ^ t ^^^ 2 ^ β := by
      rw [hq', gray_pair, hg1, ctlOf_xor_comm]
    rw [hg1] at ih'
    rw [hg2, ctlOf_flip]
    have := hstep β t (gray p) (by omega) ht (by omega)
    refine Derivable.trans ?_ this
    simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons,
      List.prod_nil, List.cons_append, List.singleton_append, mul_one]
    exact dleft _ (dright _ ih')

end QCert.RealCliffordCH.Sec8.E
