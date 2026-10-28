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
