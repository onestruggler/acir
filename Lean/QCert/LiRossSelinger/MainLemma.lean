/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20 (the Main Lemma for basic edges)

The case distinction of Figure 9 of the paper, at a state `s ≠ 1` and a
basic generator `G` that does not raise the level:

* `G = X_[x,x+1]`: `k = 0` (`squareZ_X`); `k > 0` with the transposition
  renaming the syllable (`squareX_rename`: Subcases 1.2.1, 1.2.2.1,
  1.2.2.2, 1.2.2.3 with `u_e` even), with both `x` and `x + 1` among the
  first four odd entries (`squareX_pair'`, Subcase 1.2.3), and with `d = x`
  and `u_{x+1}` odd (`squareX_odd`, Subcase 1.2.2.3 with `u_e` odd);
* `G = (−1)_[0]`: `k = 0` (`squareZ_N`), `k > 0` (`squareN_in`,
  `squareN_out`);
* `G = K_[0,1,2,3]`: `k = 0` (`squareZ_K`), `k > 0` with no first odd
  entry among `0, …, 3` (`squareK_disj`, Subcase 3.2.1) and with one
  (`squareK_meet`, Subcases 3.2.2–3.2.5).

`squareX_odd` is not proved yet.
-/
import QCert.LiRossSelinger.CaseKMeet

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-- The first four odd entries of a state at `k > 0`, as variables. -/
theorem first_four {s : O_ZHalf n} (hs : s ≠ 1) (hk : 0 < lde s) :
    ∃ (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d),
      a ∈ oddS s ∧ b ∈ oddS s ∧ c ∈ oddS s ∧ d ∈ oddS s ∧
      ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r := by
  have h4 := card_oddS s (pivot_pos hs) hk
  exact ⟨_, _, _, _, firstOdd_lt s h4 (by decide), firstOdd_lt s h4 (by decide),
    firstOdd_lt s h4 (by decide), firstOdd_mem s h4 0, firstOdd_mem s h4 1, firstOdd_mem s h4 2,
    firstOdd_mem s h4 3, rest_of_firstOdd s h4⟩

/-- The conclusion of Lemma A.20 at `s` and `G`. -/
abbrev Closes (s : O_ZHalf n) (g : Gen n) : Prop :=
  ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
    Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n g * s)) * FreeMonoid.of g)
      (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s))

/-- Subcase 1.2.2.3 with `u_e` odd: `x = d` and `x + 1` is the fifth odd entry.
**Not proved yet.** -/
theorem squareX_odd {s : O_ZHalf n} (hs : s ≠ 1) {x y : Fin n} (hxy : x < y)
    (hy : y.val = x.val + 1) (hle : level (sem n (Gen.x x y hxy) * s) ≤ level s)
    (hk : 0 < lde s) {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r)
    (h2 : d = x ∧ y ∈ oddS s) : Closes s (Gen.x x y hxy) := by
  sorry

/-- Subcases 3.2.2–3.2.5: `G = K_[0,1,2,3]` at `k > 0`, with the first odd
entry `a ≤ 3` (`CaseKMeet.squareK_meet'`). -/
theorem squareK_meet {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (hbasic : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) (h3a : a.val ≤ 3) :
    Closes s (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) :=
  squareK_meet' hs h₁ h₂ h₃ hbasic hle hk hab hbc hcd ha hb hc hd hrest h3a

/-- Case 3.2: `G = K_[0,1,2,3]` at `k > 0`. -/
theorem squareK_pos {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (hbasic : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s) :
    Closes s (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hrest⟩ := first_four hs hk
  by_cases h3a : 3 < a.val
  · exact squareK_disj hs h₁ h₂ h₃ hle hk hab hbc hcd ha hb hc hd hrest
      (Fin.lt_def.2 (by omega))
  · exact squareK_meet hs h₁ h₂ h₃ hbasic hle hk hab hbc hcd ha hb hc hd hrest (by omega)

/-- Lemma A.20 for the basic edges that do not raise the level. -/
theorem mainLemmaBasic_cases : MainLemmaBasic n := by
  intro s g hbas hs hle
  cases g with
  | neg z =>
    have hz0 : z.val = 0 := hbas
    by_cases hk : lde s = 0
    · exact squareZ_N hs hk hz0 hle
    have hk0 : 0 < lde s := Nat.pos_of_ne_zero hk
    obtain ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hrest⟩ := first_four hs hk0
    by_cases hz : z ∈ [a, b, c, d]
    · have hza : z = a := by
        have := Fin.lt_def.1 hab; have := Fin.lt_def.1 hbc; have := Fin.lt_def.1 hcd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · rfl
        all_goals exact absurd hz0 (by omega)
      subst hza
      exact squareN_in hs hle hk0 hab hbc hcd ha hb hc hd hrest
    · exact squareN_out hs hle hk0 hab hbc hcd ha hb hc hd hrest hz
  | x x y hxy =>
    have hy : y.val = x.val + 1 := hbas
    by_cases hk : lde s = 0
    · exact squareZ_X hs hk hxy hy hle
    have hk0 : 0 < lde s := Nat.pos_of_ne_zero hk
    obtain ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hrest⟩ := first_four hs hk0
    by_cases h1 : x ∈ [a, b, c, d] ∧ y ∈ [a, b, c, d]
    · exact squareX_pair' hs hxy hy hle hk0 hab hbc hcd ha hb hc hd hrest h1
    by_cases h2 : d = x ∧ y ∈ oddS s
    · exact squareX_odd hs hxy hy hle hk0 hab hbc hcd ha hb hc hd hrest h2
    exact squareX_rename hs hxy hy hle hk0 hab hbc hcd ha hb hc hd hrest h1 h2
  | k a₀ a₁ a₂ a₃ h₁ h₂ h₃ =>
    by_cases hk : lde s = 0
    · obtain ⟨e0, e1, e2, e3⟩ : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3 := hbas
      refine squareZ_K hs hk h₁ h₂ h₃ (fun r hr => ?_) hle
      have := Fin.le_def.1 hr
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      have : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 := by omega
      rcases this with h | h | h | h
      · left; exact Fin.ext (by omega)
      · right; left; exact Fin.ext (by omega)
      · right; right; left; exact Fin.ext (by omega)
      · right; right; right; exact Fin.ext (by omega)
    · exact squareK_pos hs h₁ h₂ h₃ hbas hle (Nat.pos_of_ne_zero hk)

end QCert.LiRossSelinger
