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

theorem xor4_tau (z1 z2 z3 z4 : ℤ) (o1 : z1 % 2 = 1) (o2 : z2 % 2 = 1) (o3 : z3 % 2 = 1)
    (o4 : z4 % 2 = 1) :
    xor (xor (xor (tau z1) (tau z2)) (tau z3)) (tau z4) = decide ((z1 + z2 + z3 + z4) % 4 = 2) := by
  unfold tau
  by_cases h1 : z1 % 4 = 3 <;> by_cases h2 : z2 % 4 = 3 <;> by_cases h3 : z3 % 4 = 3 <;>
    by_cases h4 : z4 % 4 = 3 <;> simp [h1, h2, h3, h4] <;> omega

theorem ne_of_val {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- Lemma A.3 with `a, b = 0, 1`: the odd entries of `K s` and the parity of the signs. -/
theorem par_01 (w0 w1 w2 w3 : ℤ) (oi : w0 % 2 = 1) (oj : w1 % 2 = 1) (ek : w2 % 2 = 0)
    (el : w3 % 2 = 0) :
    ((w0 + w1 + w2 + w3) / 2 % 2 = 1 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 1 ∧ (w0 - w1 + w2 - w3) / 2 % 2 = 0 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 0 ∧
      ((w0 + w1 + w2 + w3) / 2 + (w0 + w1 - w2 - w3) / 2 + w0 + w1) % 4 = 0) ∨
    ((w0 - w1 + w2 - w3) / 2 % 2 = 1 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 1 ∧ (w0 + w1 + w2 + w3) / 2 % 2 = 0 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 0 ∧
      ((w0 - w1 + w2 - w3) / 2 + (w0 - w1 - w2 + w3) / 2 + w0 + w1) % 4 = 2) := by
  omega

/-- Subcase 3.2.3 with `a, b = 0, 1` (from `0`). -/
theorem two_01 {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ c d : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃) (h₄ : a₃ < c) (h₅ : c < d)
    (hv : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (ha : a₀ ∈ oddS s) (hb : a₁ ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a₀ ∨ r = a₁ ∨ r = c ∨ r = d ∨ d < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  obtain ⟨e0, e1, e2, e3⟩ := hv
  have hU := pivot_pos hs
  have vc := Fin.lt_def.1 h₄; have vd := Fin.lt_def.1 h₅
  have oi := Int.odd_iff.1 ((mem_oddS_iff _).1 ha)
  have oj := Int.odd_iff.1 ((mem_oddS_iff _).1 hb)
  have ek : wint s a₂ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have el : wint s a₃ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have hsylls := syll_eq_pos s hU hk h₁ ((h₂.trans h₃).trans h₄) h₅ ha hb hc hd hrest
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  obtain ⟨u', hcV, hv0, hv1, hv2, hv3, hout⟩ := kcol h₁ h₂ h₃ hsum
  have low4 : ∀ {r : Fin n}, r ≤ a₃ → r = a₀ ∨ r = a₁ ∨ r = a₂ ∨ r = a₃ := fun {r} hr => by
    have := Fin.le_def.1 hr
    simp only [Fin.ext_iff]; omega
  rcases par_01 _ _ _ _ oi oj ek el with hp | hp
  · rw [← hv0, ← hv2, ← hv1, ← hv3] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₀) (b := a₁) (α := a₀)
      (β := a₂) h₁ ((h₂.trans h₃).trans h₄) (h₁.trans h₂) (h₃.trans h₄) (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_0102 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)
  · rw [← hv1, ← hv3, ← hv0, ← hv2] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₀) (b := a₁) (α := a₁)
      (β := a₃) h₁ ((h₂.trans h₃).trans h₄) (h₂.trans h₃) h₄ (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_0113 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)

/-- Lemma A.3 with `a, b = 0, 2`: the odd entries of `K s` and the parity of the signs. -/
theorem par_02 (w0 w1 w2 w3 : ℤ) (oi : w0 % 2 = 1) (oj : w2 % 2 = 1) (ek : w1 % 2 = 0)
    (el : w3 % 2 = 0) :
    ((w0 + w1 + w2 + w3) / 2 % 2 = 1 ∧ (w0 - w1 + w2 - w3) / 2 % 2 = 1 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 0 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 0 ∧
      ((w0 + w1 + w2 + w3) / 2 + (w0 - w1 + w2 - w3) / 2 + w0 + w2) % 4 = 0) ∨
    ((w0 + w1 - w2 - w3) / 2 % 2 = 1 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 1 ∧ (w0 + w1 + w2 + w3) / 2 % 2 = 0 ∧ (w0 - w1 + w2 - w3) / 2 % 2 = 0 ∧
      ((w0 + w1 - w2 - w3) / 2 + (w0 - w1 - w2 + w3) / 2 + w0 + w2) % 4 = 2) := by
  omega

/-- Subcase 3.2.3 with `a, b = 0, 2` (from `0`). -/
theorem two_02 {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ c d : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃) (h₄ : a₃ < c) (h₅ : c < d)
    (hv : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (ha : a₀ ∈ oddS s) (hb : a₂ ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a₀ ∨ r = a₂ ∨ r = c ∨ r = d ∨ d < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  obtain ⟨e0, e1, e2, e3⟩ := hv
  have hU := pivot_pos hs
  have vc := Fin.lt_def.1 h₄; have vd := Fin.lt_def.1 h₅
  have oi := Int.odd_iff.1 ((mem_oddS_iff _).1 ha)
  have oj := Int.odd_iff.1 ((mem_oddS_iff _).1 hb)
  have ek : wint s a₁ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have el : wint s a₃ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have hsylls := syll_eq_pos s hU hk (h₁.trans h₂) (h₃.trans h₄) h₅ ha hb hc hd hrest
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  obtain ⟨u', hcV, hv0, hv1, hv2, hv3, hout⟩ := kcol h₁ h₂ h₃ hsum
  have low4 : ∀ {r : Fin n}, r ≤ a₃ → r = a₀ ∨ r = a₁ ∨ r = a₂ ∨ r = a₃ := fun {r} hr => by
    have := Fin.le_def.1 hr
    simp only [Fin.ext_iff]; omega
  rcases par_02 _ _ _ _ oi oj ek el with hp | hp
  · rw [← hv0, ← hv1, ← hv2, ← hv3] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₀) (b := a₂) (α := a₀)
      (β := a₁) (h₁.trans h₂) (h₃.trans h₄) h₁ ((h₂.trans h₃).trans h₄) (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_0201 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)
  · rw [← hv2, ← hv3, ← hv0, ← hv1] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₀) (b := a₂) (α := a₂)
      (β := a₃) (h₁.trans h₂) (h₃.trans h₄) h₃ h₄ (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_0223 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)

/-- Lemma A.3 with `a, b = 0, 3`: the odd entries of `K s` and the parity of the signs. -/
theorem par_03 (w0 w1 w2 w3 : ℤ) (oi : w0 % 2 = 1) (oj : w3 % 2 = 1) (ek : w1 % 2 = 0)
    (el : w2 % 2 = 0) :
    ((w0 + w1 + w2 + w3) / 2 % 2 = 1 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 1 ∧ (w0 - w1 + w2 - w3) / 2 % 2 = 0 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 0 ∧
      ((w0 + w1 + w2 + w3) / 2 + (w0 - w1 - w2 + w3) / 2 + w0 + w3) % 4 = 0) ∨
    ((w0 - w1 + w2 - w3) / 2 % 2 = 1 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 1 ∧ (w0 + w1 + w2 + w3) / 2 % 2 = 0 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 0 ∧
      ((w0 - w1 + w2 - w3) / 2 + (w0 + w1 - w2 - w3) / 2 + w0 + w3) % 4 = 2) := by
  omega

/-- Subcase 3.2.3 with `a, b = 0, 3` (from `0`). -/
theorem two_03 {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ c d : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃) (h₄ : a₃ < c) (h₅ : c < d)
    (hv : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (ha : a₀ ∈ oddS s) (hb : a₃ ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a₀ ∨ r = a₃ ∨ r = c ∨ r = d ∨ d < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  obtain ⟨e0, e1, e2, e3⟩ := hv
  have hU := pivot_pos hs
  have vc := Fin.lt_def.1 h₄; have vd := Fin.lt_def.1 h₅
  have oi := Int.odd_iff.1 ((mem_oddS_iff _).1 ha)
  have oj := Int.odd_iff.1 ((mem_oddS_iff _).1 hb)
  have ek : wint s a₁ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have el : wint s a₂ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have hsylls := syll_eq_pos s hU hk (h₁.trans (h₂.trans h₃)) h₄ h₅ ha hb hc hd hrest
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  obtain ⟨u', hcV, hv0, hv1, hv2, hv3, hout⟩ := kcol h₁ h₂ h₃ hsum
  have low4 : ∀ {r : Fin n}, r ≤ a₃ → r = a₀ ∨ r = a₁ ∨ r = a₂ ∨ r = a₃ := fun {r} hr => by
    have := Fin.le_def.1 hr
    simp only [Fin.ext_iff]; omega
  rcases par_03 _ _ _ _ oi oj ek el with hp | hp
  · rw [← hv0, ← hv3, ← hv1, ← hv2] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₀) (b := a₃) (α := a₀)
      (β := a₃) (h₁.trans (h₂.trans h₃)) h₄ (h₁.trans (h₂.trans h₃)) h₄ (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_0303 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)
  · rw [← hv1, ← hv2, ← hv0, ← hv3] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₀) (b := a₃) (α := a₁)
      (β := a₂) (h₁.trans (h₂.trans h₃)) h₄ h₂ (h₃.trans h₄) (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_0312 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)

/-- Lemma A.3 with `a, b = 1, 2`: the odd entries of `K s` and the parity of the signs. -/
theorem par_12 (w0 w1 w2 w3 : ℤ) (oi : w1 % 2 = 1) (oj : w2 % 2 = 1) (ek : w0 % 2 = 0)
    (el : w3 % 2 = 0) :
    ((w0 + w1 + w2 + w3) / 2 % 2 = 1 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 1 ∧ (w0 - w1 + w2 - w3) / 2 % 2 = 0 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 0 ∧
      ((w0 + w1 + w2 + w3) / 2 + (w0 - w1 - w2 + w3) / 2 + w1 + w2) % 4 = 2) ∨
    ((w0 - w1 + w2 - w3) / 2 % 2 = 1 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 1 ∧ (w0 + w1 + w2 + w3) / 2 % 2 = 0 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 0 ∧
      ((w0 - w1 + w2 - w3) / 2 + (w0 + w1 - w2 - w3) / 2 + w1 + w2) % 4 = 0) := by
  omega

/-- Subcase 3.2.3 with `a, b = 1, 2` (from `0`). -/
theorem two_12 {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ c d : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃) (h₄ : a₃ < c) (h₅ : c < d)
    (hv : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (ha : a₁ ∈ oddS s) (hb : a₂ ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a₁ ∨ r = a₂ ∨ r = c ∨ r = d ∨ d < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  obtain ⟨e0, e1, e2, e3⟩ := hv
  have hU := pivot_pos hs
  have vc := Fin.lt_def.1 h₄; have vd := Fin.lt_def.1 h₅
  have oi := Int.odd_iff.1 ((mem_oddS_iff _).1 ha)
  have oj := Int.odd_iff.1 ((mem_oddS_iff _).1 hb)
  have ek : wint s a₀ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have el : wint s a₃ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have hsylls := syll_eq_pos s hU hk h₂ (h₃.trans h₄) h₅ ha hb hc hd hrest
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  obtain ⟨u', hcV, hv0, hv1, hv2, hv3, hout⟩ := kcol h₁ h₂ h₃ hsum
  have low4 : ∀ {r : Fin n}, r ≤ a₃ → r = a₀ ∨ r = a₁ ∨ r = a₂ ∨ r = a₃ := fun {r} hr => by
    have := Fin.le_def.1 hr
    simp only [Fin.ext_iff]; omega
  rcases par_12 _ _ _ _ oi oj ek el with hp | hp
  · rw [← hv0, ← hv3, ← hv1, ← hv2] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₁) (b := a₂) (α := a₀)
      (β := a₃) h₂ (h₃.trans h₄) (h₁.trans (h₂.trans h₃)) h₄ (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_1203 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)
  · rw [← hv1, ← hv2, ← hv0, ← hv3] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₁) (b := a₂) (α := a₁)
      (β := a₂) h₂ (h₃.trans h₄) h₂ (h₃.trans h₄) (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_1212 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)

/-- Lemma A.3 with `a, b = 1, 3`: the odd entries of `K s` and the parity of the signs. -/
theorem par_13 (w0 w1 w2 w3 : ℤ) (oi : w1 % 2 = 1) (oj : w3 % 2 = 1) (ek : w0 % 2 = 0)
    (el : w2 % 2 = 0) :
    ((w0 + w1 + w2 + w3) / 2 % 2 = 1 ∧ (w0 - w1 + w2 - w3) / 2 % 2 = 1 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 0 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 0 ∧
      ((w0 + w1 + w2 + w3) / 2 + (w0 - w1 + w2 - w3) / 2 + w1 + w3) % 4 = 2) ∨
    ((w0 + w1 - w2 - w3) / 2 % 2 = 1 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 1 ∧ (w0 + w1 + w2 + w3) / 2 % 2 = 0 ∧ (w0 - w1 + w2 - w3) / 2 % 2 = 0 ∧
      ((w0 + w1 - w2 - w3) / 2 + (w0 - w1 - w2 + w3) / 2 + w1 + w3) % 4 = 0) := by
  omega

/-- Subcase 3.2.3 with `a, b = 1, 3` (from `0`). -/
theorem two_13 {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ c d : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃) (h₄ : a₃ < c) (h₅ : c < d)
    (hv : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (ha : a₁ ∈ oddS s) (hb : a₃ ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a₁ ∨ r = a₃ ∨ r = c ∨ r = d ∨ d < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  obtain ⟨e0, e1, e2, e3⟩ := hv
  have hU := pivot_pos hs
  have vc := Fin.lt_def.1 h₄; have vd := Fin.lt_def.1 h₅
  have oi := Int.odd_iff.1 ((mem_oddS_iff _).1 ha)
  have oj := Int.odd_iff.1 ((mem_oddS_iff _).1 hb)
  have ek : wint s a₀ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have el : wint s a₂ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have hsylls := syll_eq_pos s hU hk (h₂.trans h₃) h₄ h₅ ha hb hc hd hrest
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  obtain ⟨u', hcV, hv0, hv1, hv2, hv3, hout⟩ := kcol h₁ h₂ h₃ hsum
  have low4 : ∀ {r : Fin n}, r ≤ a₃ → r = a₀ ∨ r = a₁ ∨ r = a₂ ∨ r = a₃ := fun {r} hr => by
    have := Fin.le_def.1 hr
    simp only [Fin.ext_iff]; omega
  rcases par_13 _ _ _ _ oi oj ek el with hp | hp
  · rw [← hv0, ← hv1, ← hv2, ← hv3] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₁) (b := a₃) (α := a₀)
      (β := a₁) (h₂.trans h₃) h₄ h₁ ((h₂.trans h₃).trans h₄) (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_1301 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)
  · rw [← hv2, ← hv3, ← hv0, ← hv1] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₁) (b := a₃) (α := a₂)
      (β := a₃) (h₂.trans h₃) h₄ h₃ h₄ (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_1323 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)

/-- Lemma A.3 with `a, b = 2, 3`: the odd entries of `K s` and the parity of the signs. -/
theorem par_23 (w0 w1 w2 w3 : ℤ) (oi : w2 % 2 = 1) (oj : w3 % 2 = 1) (ek : w0 % 2 = 0)
    (el : w1 % 2 = 0) :
    ((w0 + w1 + w2 + w3) / 2 % 2 = 1 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 1 ∧ (w0 - w1 + w2 - w3) / 2 % 2 = 0 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 0 ∧
      ((w0 + w1 + w2 + w3) / 2 + (w0 + w1 - w2 - w3) / 2 + w2 + w3) % 4 = 2) ∨
    ((w0 - w1 + w2 - w3) / 2 % 2 = 1 ∧ (w0 - w1 - w2 + w3) / 2 % 2 = 1 ∧ (w0 + w1 + w2 + w3) / 2 % 2 = 0 ∧ (w0 + w1 - w2 - w3) / 2 % 2 = 0 ∧
      ((w0 - w1 + w2 - w3) / 2 + (w0 - w1 - w2 + w3) / 2 + w2 + w3) % 4 = 0) := by
  omega

/-- Subcase 3.2.3 with `a, b = 2, 3` (from `0`). -/
theorem two_23 {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ c d : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃) (h₄ : a₃ < c) (h₅ : c < d)
    (hv : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (ha : a₂ ∈ oddS s) (hb : a₃ ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a₂ ∨ r = a₃ ∨ r = c ∨ r = d ∨ d < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  obtain ⟨e0, e1, e2, e3⟩ := hv
  have hU := pivot_pos hs
  have vc := Fin.lt_def.1 h₄; have vd := Fin.lt_def.1 h₅
  have oi := Int.odd_iff.1 ((mem_oddS_iff _).1 ha)
  have oj := Int.odd_iff.1 ((mem_oddS_iff _).1 hb)
  have ek : wint s a₀ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have el : wint s a₁ % 2 = 0 := even_low hrest (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega)) (ne_of_val (by omega))
    (Fin.le_def.2 (by omega))
  have hsylls := syll_eq_pos s hU hk h₃ h₄ h₅ ha hb hc hd hrest
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  obtain ⟨u', hcV, hv0, hv1, hv2, hv3, hout⟩ := kcol h₁ h₂ h₃ hsum
  have low4 : ∀ {r : Fin n}, r ≤ a₃ → r = a₀ ∨ r = a₁ ∨ r = a₂ ∨ r = a₃ := fun {r} hr => by
    have := Fin.le_def.1 hr
    simp only [Fin.ext_iff]; omega
  rcases par_23 _ _ _ _ oi oj ek el with hp | hp
  · rw [← hv0, ← hv2, ← hv1, ← hv3] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₂) (b := a₃) (α := a₀)
      (β := a₂) h₃ h₄ (h₁.trans h₂) (h₃.trans h₄) (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_2302 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)
  · rw [← hv1, ← hv3, ← hv0, ← hv2] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := a₂) (b := a₃) (α := a₁)
      (β := a₃) h₃ h₄ (h₂.trans h₃) h₄ (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_2313 h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)

/-- Subcases 3.2.2–3.2.5: `G = K_[0,1,2,3]` at `k > 0`, with the first odd
entry `a ≤ 3`. -/
theorem squareK_meet' {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (hbasic : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) (h3a : a.val ≤ 3) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hbas := hbasic
  obtain ⟨e0, e1, e2, e3⟩ := hbasic
  have va := Fin.lt_def.1 hab; have vb := Fin.lt_def.1 hbc; have vc := Fin.lt_def.1 hcd
  have p0 := par_entry ha hb hc hd hrest a₀ (Fin.le_def.2 (by omega))
  have p1 := par_entry ha hb hc hd hrest a₁ (Fin.le_def.2 (by omega))
  have p2 := par_entry ha hb hc hd hrest a₂ (Fin.le_def.2 (by omega))
  have p3 := par_entry ha hb hc hd hrest a₃ (Fin.le_def.2 (by omega))
  by_cases hd3 : d.val ≤ 3
  · -- Subcase 3.2.5
    obtain rfl : a = a₀ := Fin.ext (by omega)
    obtain rfl : b = a₁ := Fin.ext (by omega)
    obtain rfl : c = a₂ := Fin.ext (by omega)
    obtain rfl : d = a₃ := Fin.ext (by omega)
    exact squareK_four hs h₁ h₂ h₃ hle hk ha hb hc hd hrest
  by_cases hb3 : b.val ≤ 3
  · by_cases hc3 : c.val ≤ 3
    · -- Subcase 3.2.4: three odd entries among `0, …, 3`
      exfalso
      apply k_odd_raises hs h₁ h₂ h₃ hle hk
      split_ifs at p0 p1 p2 p3 <;> omega
    -- Subcase 3.2.3
    have h₄ : a₃ < c := Fin.lt_def.2 (by omega)
    have hcases : (a.val = 0 ∧ b.val = 1) ∨ (a.val = 0 ∧ b.val = 2) ∨ (a.val = 0 ∧ b.val = 3) ∨
        (a.val = 1 ∧ b.val = 2) ∨ (a.val = 1 ∧ b.val = 3) ∨ (a.val = 2 ∧ b.val = 3) := by omega
    rcases hcases with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
    · obtain rfl : a = a₀ := Fin.ext (by omega)
      obtain rfl : b = a₁ := Fin.ext (by omega)
      exact two_01 hs h₁ h₂ h₃ h₄ hcd hbas hle hk ha hb hc hd hrest
    · obtain rfl : a = a₀ := Fin.ext (by omega)
      obtain rfl : b = a₂ := Fin.ext (by omega)
      exact two_02 hs h₁ h₂ h₃ h₄ hcd hbas hle hk ha hb hc hd hrest
    · obtain rfl : a = a₀ := Fin.ext (by omega)
      obtain rfl : b = a₃ := Fin.ext (by omega)
      exact two_03 hs h₁ h₂ h₃ h₄ hcd hbas hle hk ha hb hc hd hrest
    · obtain rfl : a = a₁ := Fin.ext (by omega)
      obtain rfl : b = a₂ := Fin.ext (by omega)
      exact two_12 hs h₁ h₂ h₃ h₄ hcd hbas hle hk ha hb hc hd hrest
    · obtain rfl : a = a₁ := Fin.ext (by omega)
      obtain rfl : b = a₃ := Fin.ext (by omega)
      exact two_13 hs h₁ h₂ h₃ h₄ hcd hbas hle hk ha hb hc hd hrest
    · obtain rfl : a = a₂ := Fin.ext (by omega)
      obtain rfl : b = a₃ := Fin.ext (by omega)
      exact two_23 hs h₁ h₂ h₃ h₄ hcd hbas hle hk ha hb hc hd hrest
  · -- Subcase 3.2.2: one odd entry among `0, …, 3`
    exfalso
    apply k_odd_raises hs h₁ h₂ h₃ hle hk
    split_ifs at p0 p1 p2 p3 <;> omega

end QCert.LiRossSelinger
