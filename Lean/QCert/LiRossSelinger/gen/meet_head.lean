/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcases 3.2.2–3.2.5: `K_[0,1,2,3]` meeting the first odd entries

`G = K_[0,1,2,3]` at `k > 0` with the first odd entry `a ≤ 3`.  With one or
three of the first four odd entries among `0, …, 3` (Subcases 3.2.2, 3.2.4)
the four entries have an odd sum, `K` raises the least denominator exponent
and the level (`k_odd_raises`); these are excluded.  With all four
(Subcase 3.2.5) see `CaseK4`.  With two, `a < b ≤ 3 < c` (Subcase 3.2.3),
`K s` has exactly two odd entries `α < β` among `0, …, 3` (Lemma A.3: two
choices for each `a, b`), its syllable is `K_[α,β,c,d]` with signs, and the
square closes by `X K_[0,1,2,c] Y` (`Rel323`, `finish323`); the parity of the
four signs of `α, β, a, b` is fixed by `a, b, α, β` and found by `omega`.
`two_ij` is the case `a, b = i, j`; they are generated (scratch).
-/
import QCert.LiRossSelinger.CaseK2
import QCert.LiRossSelinger.CaseK4
import QCert.LiRossSelinger.Rel323

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

theorem even_low {s : O_ZHalf n} {a b c d r : Fin n}
    (hrest : ∀ x ∈ oddS s, x = a ∨ x = b ∨ x = c ∨ x = d ∨ d < x) (ha : r ≠ a) (hb : r ≠ b)
    (hc : r ≠ c) (hd : r ≠ d) (hrd : r ≤ d) : wint s r % 2 = 0 := by
  by_contra h
  have ho : r ∈ oddS s := (mem_oddS_iff r).2 (Int.odd_iff.2 (by omega))
  rcases hrest r ho with e | e | e | e | e
  exacts [ha e, hb e, hc e, hd e, absurd hrd (not_le.2 e)]

theorem par_entry {s : O_ZHalf n} {a b c d : Fin n} (ha : a ∈ oddS s) (hb : b ∈ oddS s)
    (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ x ∈ oddS s, x = a ∨ x = b ∨ x = c ∨ x = d ∨ d < x) (r : Fin n) (hrd : r ≤ d) :
    wint s r % 2 = if r.val = a.val ∨ r.val = b.val ∨ r.val = c.val ∨ r.val = d.val then 1
      else 0 := by
  split_ifs with h
  · rcases h with h | h | h | h
    · rw [Fin.ext h]; exact Int.odd_iff.1 ((mem_oddS_iff a).1 ha)
    · rw [Fin.ext h]; exact Int.odd_iff.1 ((mem_oddS_iff b).1 hb)
    · rw [Fin.ext h]; exact Int.odd_iff.1 ((mem_oddS_iff c).1 hc)
    · rw [Fin.ext h]; exact Int.odd_iff.1 ((mem_oddS_iff d).1 hd)
  · simp only [not_or] at h
    exact even_low hrest (fun e => h.1 (congrArg Fin.val e)) (fun e => h.2.1 (congrArg Fin.val e))
      (fun e => h.2.2.1 (congrArg Fin.val e)) (fun e => h.2.2.2 (congrArg Fin.val e)) hrd

/-- The column of `K_[0,1,2,3] s` when the sum of the four entries is even. -/
theorem kcol {s : O_ZHalf n} {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁) (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃) :
    ∃ u' : Fin n → ℤ, IsCol (gact (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) (pcol s)) (lde s) u' ∧
      u' a₀ = (wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃) / 2 ∧
      u' a₁ = (wint s a₀ - wint s a₁ + wint s a₂ - wint s a₃) / 2 ∧
      u' a₂ = (wint s a₀ + wint s a₁ - wint s a₂ - wint s a₃) / 2 ∧
      u' a₃ = (wint s a₀ - wint s a₁ - wint s a₂ + wint s a₃) / 2 ∧
      ∀ r, a₃ < r → u' r = wint s r := by
  have d01 : a₀ ≠ a₁ := ne_of_lt h₁
  have d02 : a₀ ≠ a₂ := ne_of_lt (h₁.trans h₂)
  have d03 : a₀ ≠ a₃ := ne_of_lt (h₁.trans (h₂.trans h₃))
  have d12 : a₁ ≠ a₂ := ne_of_lt h₂
  have d13 : a₁ ≠ a₃ := ne_of_lt (h₂.trans h₃)
  have d23 : a₂ ≠ a₃ := ne_of_lt h₃
  refine ⟨_, isCol_k (isCol_pcol s) h₁ h₂ h₃ hsum, by simp, by simp [d01.symm],
    by simp [d02.symm, d12.symm], by simp [d03.symm, d13.symm, d23.symm], fun r hr => ?_⟩
  have e3 : r ≠ a₃ := (ne_of_lt hr).symm
  have e2 : r ≠ a₂ := (ne_of_lt (h₃.trans hr)).symm
  have e1 : r ≠ a₁ := (ne_of_lt (h₂.trans (h₃.trans hr))).symm
  have e0 : r ≠ a₀ := (ne_of_lt (h₁.trans (h₂.trans (h₃.trans hr)))).symm
  simp [e0, e1, e2, e3]

/-- Subcase 3.2.3, given the two odd entries `α < β` of `K s` among `0, …, 3`
and the derivation on `0, …, 3, c, d`. -/
theorem finish323 {s : O_ZHalf n} (hs : s ≠ 1) (hk : 0 < lde s) {a₀ a₁ a₂ a₃ c d : Fin n}
    (h₁ : a₀ < a₁) (h₂ : a₁ < a₂) (h₃ : a₂ < a₃) (h₄ : a₃ < c) (h₅ : c < d)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s)
    {a b α β : Fin n} (hab : a < b) (hbc : b < c) (hαβ : α < β) (hβc : β < c) (hb3 : b ≤ a₃)
    (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hsylls : syll s = Gen.k a b c d hab hbc h₅ :: signs s [a, b, c, d])
    {u' : Fin n → ℤ} (hcV : IsCol (gact (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) (pcol s)) (lde s) u')
    (hα : Odd (u' α)) (hβ : Odd (u' β)) (hout : ∀ r, a₃ < r → u' r = wint s r)
    (hlow : ∀ r : Fin n, r ≤ a₃ → Odd (u' r) → r = α ∨ r = β)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r)
    (hder : ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k α β c d hαβ hβc h₅ ::
          (negw (tau (u' α)) α ++ negw (tau (u' β)) β) ++ [Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃]))
        (FreeMonoid.ofList (Xw ++ Gen.k a₀ a₁ a₂ c h₁ h₂ (h₃.trans h₄) :: Yw ++
          Gen.k a b c d hab hbc h₅ :: (negw (tau (wint s a)) a ++ negw (tau (wint s b)) b)))) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  have hJ : a₃.val < pivotJ s := extent_lt_of_le hs hle
  obtain ⟨hpV, hcolV, hkV⟩ := state_gen hs (g := Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) hJ hcV hk hα
  have hcV' : IsCol (pcol (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s))
      (lde (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) u' := by rw [hcolV, hkV]; exact hcV
  have hwV : ∀ r, wint (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) r = u' r :=
    fun r => wint_eq hcV' r
  have hmemV : ∀ r, r ∈ oddS (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ↔ Odd (u' r) :=
    fun r => by rw [mem_oddS_iff, hwV]
  have hco : Odd (u' c) := by rw [hout c h₄]; exact (mem_oddS_iff c).1 hc
  have hdo : Odd (u' d) := by rw [hout d (h₄.trans h₅)]; exact (mem_oddS_iff d).1 hd
  have hrestV : ∀ r ∈ oddS (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s),
      r = α ∨ r = β ∨ r = c ∨ r = d ∨ d < r := by
    intro r hr
    rw [hmemV] at hr
    by_cases hr3 : r ≤ a₃
    · rcases hlow r hr3 hr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · push Not at hr3
      rw [hout r hr3] at hr
      rcases hrest r ((mem_oddS_iff r).2 hr) with h | h | h | h | h
      · exfalso; subst h; exact absurd (lt_of_lt_of_le hab hb3) (not_lt.2 hr3.le)
      · exfalso; subst h; exact absurd hb3 (not_le.2 hr3)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hsyllV := syll_eq_pos _ (by rw [hpV]; exact hU) (by rw [hkV]; exact hk) hαβ hβc h₅
    ((hmemV α).2 hα) ((hmemV β).2 hβ) ((hmemV c).2 hco) ((hmemV d).2 hdo) hrestV
  have hcd : signs (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) [c, d] = signs s [c, d] :=
    signs_congr s _ [c, d] (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hwV, hout _ h₄]
      · rw [hwV, hout _ (h₄.trans h₅)])
  obtain ⟨Xw, Yw, hXY, hD⟩ := hder
  have hdJ : d.val < pivotJ s := le_pidx_of_odd hs hd
  have hsp : ∀ x ∈ Xw ++ Yw, SPBelow s x :=
    fun x hx => ⟨(hXY x hx).1, lt_of_le_of_lt (hXY x hx).2 hdJ⟩
  refine square_two hs hk hle (c := c) (d := d) ?_ (Gen.k a b c d hab hbc h₅)
    (Gen.k α β c d hαβ hβc h₅) (negw (tau (wint s a)) a ++ negw (tau (wint s b)) b)
    (negw (tau (u' α)) α ++ negw (tau (u' β)) β) (by rw [hsylls, signs_two])
    (by rw [hsyllV, signs_two, hcd, hwV, hwV]) Xw Yw _
    (fun x hx => hsp x (List.mem_append_left _ hx)) (fun x hx => hsp x (List.mem_append_right _ hx))
    hD
  intro z hz
  have hz' : a₃ < z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact h₄
    · exact h₄.trans h₅
  exact Derivable.of (Table1.r2e z a₀ a₁ a₂ a₃ h₁ h₂ h₃ (nd5 h₁ h₂ h₃ hz'))
