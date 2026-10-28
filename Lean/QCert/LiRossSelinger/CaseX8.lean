/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcase 1.2.2.3 with `u_e` odd: the two eight-entry diagrams

`G = X_[d,e]` with `e = d + 1` the fifth odd entry.  With `f, g, h` the next
three odd entries, both `s` and `r = G s` have the first eight odd entries
`a, …, h`, their first two syllables are on `a, b, c, d` and `e, f, g, h`, and
the square closes by

  `P = W⁻¹ K_[a,b,c,d] K_[e,f,g,h] X_[d,e] K_[e,f,g,h] K_[a,b,c,d] W · N_t`

(`N_t` the syllable of `t`) with `W = (−1)_[a] (−1)_[e] X_[a,e]` when the sum
of the eight entries made `≡ 1 (mod 4)` is `≡ 4 (mod 8)`, and
`W = (−1)_[a] (−1)_[h] X_[a,h]` when it is `≡ 0 (mod 8)` (the paper's
`ū ᵀ ū ≡ 0, 8 (mod 16)`, Lemmas A.8–A.10).  The relations are (6a) and
Proposition A.16 (`Rel1223`).  The inner states of `P` lie below `s`: after
the two syllables the eight entries are even, `W` keeps them so, and the two
`K`s keep them even by the parity condition (`eight`); the states on the
side of `q` are the same computation at `r`.
-/
import QCert.LiRossSelinger.PathSP
import QCert.LiRossSelinger.Rel1223

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-! ## Integer columns along a word, entry by entry -/

theorem step_neg {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (hc : IsCol v k u) (a : Fin n) :
    ∃ u', IsCol (gact (.neg a) v) k u' ∧ u' a = -u a ∧ ∀ r, r ≠ a → u' r = u r :=
  ⟨_, isCol_neg hc a, by simp, fun r hr => by simp [hr]⟩

theorem step_negw {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (hc : IsCol v k u) (t : Bool)
    (a : Fin n) :
    ∃ u', IsCol (wact (negw t a) v) k u' ∧ u' a = (if t then -u a else u a) ∧
      ∀ r, r ≠ a → u' r = u r := by
  cases t
  · exact ⟨u, hc, by simp, fun _ _ => rfl⟩
  · obtain ⟨u', h1, h2, h3⟩ := step_neg hc a
    exact ⟨u', by simpa [negw, wact] using h1, by simpa using h2, h3⟩

theorem step_x {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (hc : IsCol v k u) {a b : Fin n}
    (hab : a < b) :
    ∃ u', IsCol (gact (.x a b hab) v) k u' ∧ u' a = u b ∧ u' b = u a ∧
      ∀ r, r ≠ a → r ≠ b → u' r = u r :=
  ⟨_, isCol_x hc hab, by simp, by simp, fun r h1 h2 => by
    simp [Equiv.swap_apply_of_ne_of_ne h1 h2]⟩

theorem step_k {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (hc : IsCol v k u) {a b c d : Fin n}
    (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) (hev : 2 ∣ u a + u b + u c + u d) :
    ∃ u', IsCol (gact (.k a b c d h₁ h₂ h₃) v) k u' ∧
      u' a = (u a + u b + u c + u d) / 2 ∧ u' b = (u a - u b + u c - u d) / 2 ∧
      u' c = (u a + u b - u c - u d) / 2 ∧ u' d = (u a - u b - u c + u d) / 2 ∧
      ∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → u' r = u r := by
  have d01 : a ≠ b := ne_of_lt h₁
  have d02 : a ≠ c := ne_of_lt (h₁.trans h₂)
  have d03 : a ≠ d := ne_of_lt (h₁.trans (h₂.trans h₃))
  have d12 : b ≠ c := ne_of_lt h₂
  have d13 : b ≠ d := ne_of_lt (h₂.trans h₃)
  have d23 : c ≠ d := ne_of_lt h₃
  exact ⟨_, isCol_k hc h₁ h₂ h₃ hev, by simp, by simp [d01.symm],
    by simp [d02.symm, d12.symm], by simp [d03.symm, d13.symm, d23.symm],
    fun r e0 e1 e2 e3 => by simp [e0, e1, e2, e3]⟩

theorem fix4_tau (z : ℤ) : (if tau z then -z else z) = fix4 z := by
  unfold tau fix4; by_cases h : z % 4 = 3 <;> simp [h]

theorem wact_append (l₁ l₂ : List (Gen n)) (v : Fin n → ℝ) :
    wact (l₁ ++ l₂) v = wact l₁ (wact l₂ v) := by
  simp [wact, List.foldr_append]

/-- The integer column after a `k > 0` syllable. -/
theorem isCol_syll {U : O_ZHalf n} (hU : U ≠ 1) (hk : 0 < lde U) {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS U) (hb : b ∈ oddS U) (hc : c ∈ oddS U) (hd : d ∈ oddS U)
    (hrest : ∀ r ∈ oddS U, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) :
    syll U = Gen.k a b c d hab hbc hcd :: signs U [a, b, c, d] ∧
    ∃ u1 : Fin n → ℤ, IsCol (wact (syll U) (pcol U)) (lde U) u1 ∧
      u1 a = (fix4 (wint U a) + fix4 (wint U b) + fix4 (wint U c) + fix4 (wint U d)) / 2 ∧
      u1 b = (fix4 (wint U a) - fix4 (wint U b) + fix4 (wint U c) - fix4 (wint U d)) / 2 ∧
      u1 c = (fix4 (wint U a) + fix4 (wint U b) - fix4 (wint U c) - fix4 (wint U d)) / 2 ∧
      u1 d = (fix4 (wint U a) - fix4 (wint U b) - fix4 (wint U c) + fix4 (wint U d)) / 2 ∧
      ∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → u1 r = wint U r := by
  have hs := syll_eq_pos U (pivot_pos hU) hk hab hbc hcd ha hb hc hd hrest
  refine ⟨hs, ?_⟩
  have d01 : a ≠ b := ne_of_lt hab
  have d02 : a ≠ c := ne_of_lt (hab.trans hbc)
  have d03 : a ≠ d := ne_of_lt (hab.trans (hbc.trans hcd))
  have d12 : b ≠ c := ne_of_lt hbc
  have d13 : b ≠ d := ne_of_lt (hbc.trans hcd)
  have d23 : c ≠ d := ne_of_lt hcd
  rw [hs, wact_cons, signs4, wact_append, wact_append, wact_append]
  obtain ⟨u4, c4, v4, o4⟩ := step_negw (isCol_pcol U) (tau (wint U d)) d
  obtain ⟨u3, c3, v3, o3⟩ := step_negw c4 (tau (wint U c)) c
  obtain ⟨u2, c2, v2, o2⟩ := step_negw c3 (tau (wint U b)) b
  obtain ⟨u1, c1, v1, o1⟩ := step_negw c2 (tau (wint U a)) a
  have ea : u1 a = fix4 (wint U a) := by rw [v1, o2 a d01, o3 a d02, o4 a d03, fix4_tau]
  have eb : u1 b = fix4 (wint U b) := by
    rw [o1 b d01.symm, v2, o3 b d12, o4 b d13, fix4_tau]
  have ec : u1 c = fix4 (wint U c) := by
    rw [o1 c d02.symm, o2 c d12.symm, v3, o4 c d23, fix4_tau]
  have ed : u1 d = fix4 (wint U d) := by
    rw [o1 d d03.symm, o2 d d13.symm, o3 d d23.symm, v4, fix4_tau]
  have hodd : ∀ x ∈ oddS U, fix4 (wint U x) % 2 = 1 := fun x hx => by
    have := fix4_mod ((mem_oddS_iff x).1 hx); omega
  have pa := hodd a ha; have pb := hodd b hb; have pc := hodd c hc; have pd := hodd d hd
  obtain ⟨u0, c0, va, vb, vc, vd, oo⟩ := step_k c1 hab hbc hcd (by rw [ea, eb, ec, ed]; omega)
  refine ⟨u0, c0, by rw [va, ea, eb, ec, ed], by rw [vb, ea, eb, ec, ed],
    by rw [vc, ea, eb, ec, ed], by rw [vd, ea, eb, ec, ed], fun r e0 e1 e2 e3 => ?_⟩
  rw [oo r e0 e1 e2 e3, o1 r e0, o2 r e1, o3 r e2, o4 r e3]

/-! ## The parity arithmetic (Lemmas A.8–A.10) -/

/-- After the two syllables (entries `ν`), `W = (−1)_[a](−1)_[e]X_[a,e]` and the
two `K`s keep the eight entries even when the sum is `≡ 4 (mod 8)`. -/
theorem par8_e (Fa Fb Fc Fd Fe Ff Fg Fh : ℤ) (pa : Fa % 4 = 1) (pb : Fb % 4 = 1)
    (pc : Fc % 4 = 1) (pd : Fd % 4 = 1) (pe : Fe % 4 = 1) (pf : Ff % 4 = 1) (pg : Fg % 4 = 1)
    (ph : Fh % 4 = 1) (hs : (Fa + Fb + Fc + Fd + Fe + Ff + Fg + Fh) % 8 = 4)
    (νa νb νc νd νe νf νg νh : ℤ) (ea : νa = (Fa + Fb + Fc + Fd) / 2)
    (eb : νb = (Fa - Fb + Fc - Fd) / 2) (ec : νc = (Fa + Fb - Fc - Fd) / 2)
    (ed : νd = (Fa - Fb - Fc + Fd) / 2) (ee : νe = (Fe + Ff + Fg + Fh) / 2)
    (ef : νf = (Fe - Ff + Fg - Fh) / 2) (eg : νg = (Fe + Ff - Fg - Fh) / 2)
    (eh : νh = (Fe - Ff - Fg + Fh) / 2) :
    νa % 2 = 0 ∧ νb % 2 = 0 ∧ νc % 2 = 0 ∧ νd % 2 = 0 ∧ νe % 2 = 0 ∧ νf % 2 = 0 ∧
      νg % 2 = 0 ∧ νh % 2 = 0 ∧ 2 ∣ -νe + νb + νc + νd ∧
      (-νe + νb + νc + νd) / 2 % 2 = 0 ∧ (-νe - νb + νc - νd) / 2 % 2 = 0 ∧
      (-νe + νb - νc - νd) / 2 % 2 = 0 ∧ (-νe - νb - νc + νd) / 2 % 2 = 0 ∧
      2 ∣ -νa + νf + νg + νh ∧
      (-νa + νf + νg + νh) / 2 % 2 = 0 ∧ (-νa - νf + νg - νh) / 2 % 2 = 0 ∧
      (-νa + νf - νg - νh) / 2 % 2 = 0 ∧ (-νa - νf - νg + νh) / 2 % 2 = 0 := by
  omega

/-- The same with `W = (−1)_[a](−1)_[h]X_[a,h]` when the sum is `≡ 0 (mod 8)`. -/
theorem par8_h (Fa Fb Fc Fd Fe Ff Fg Fh : ℤ) (pa : Fa % 4 = 1) (pb : Fb % 4 = 1)
    (pc : Fc % 4 = 1) (pd : Fd % 4 = 1) (pe : Fe % 4 = 1) (pf : Ff % 4 = 1) (pg : Fg % 4 = 1)
    (ph : Fh % 4 = 1) (hs : (Fa + Fb + Fc + Fd + Fe + Ff + Fg + Fh) % 8 = 0)
    (νa νb νc νd νe νf νg νh : ℤ) (ea : νa = (Fa + Fb + Fc + Fd) / 2)
    (eb : νb = (Fa - Fb + Fc - Fd) / 2) (ec : νc = (Fa + Fb - Fc - Fd) / 2)
    (ed : νd = (Fa - Fb - Fc + Fd) / 2) (ee : νe = (Fe + Ff + Fg + Fh) / 2)
    (ef : νf = (Fe - Ff + Fg - Fh) / 2) (eg : νg = (Fe + Ff - Fg - Fh) / 2)
    (eh : νh = (Fe - Ff - Fg + Fh) / 2) :
    νa % 2 = 0 ∧ νb % 2 = 0 ∧ νc % 2 = 0 ∧ νd % 2 = 0 ∧ νe % 2 = 0 ∧ νf % 2 = 0 ∧
      νg % 2 = 0 ∧ νh % 2 = 0 ∧ 2 ∣ -νh + νb + νc + νd ∧
      (-νh + νb + νc + νd) / 2 % 2 = 0 ∧ (-νh - νb + νc - νd) / 2 % 2 = 0 ∧
      (-νh + νb - νc - νd) / 2 % 2 = 0 ∧ (-νh - νb - νc + νd) / 2 % 2 = 0 ∧
      2 ∣ νe + νf + νg + -νa ∧
      (νe + νf + νg + -νa) / 2 % 2 = 0 ∧ (νe - νf + νg - -νa) / 2 % 2 = 0 ∧
      (νe + νf - νg - -νa) / 2 % 2 = 0 ∧ (νe - νf - νg + -νa) / 2 % 2 = 0 := by
  omega

/-! ## The first two syllables at a state with eight first odd entries -/

theorem signs_extent {U : O_ZHalf n} {l : List (Fin n)} {J : ℕ} (hl : ∀ x ∈ l, x.val < J) :
    ∀ g ∈ signs U l, extent g < J := by
  intro g hg
  obtain ⟨r, hr, rfl⟩ := mem_signs hg
  exact hl r hr

theorem eight_syll {σ : O_ZHalf n} (hσ : σ ≠ 1) (hk : 0 < lde σ) {a b c d e f g h : Fin n}
    (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) (h5 : e < f) (h6 : f < g) (h7 : g < h)
    (ha : a ∈ oddS σ) (hb : b ∈ oddS σ) (hc : c ∈ oddS σ) (hd : d ∈ oddS σ)
    (he : e ∈ oddS σ) (hf : f ∈ oddS σ) (hg : g ∈ oddS σ) (hh : h ∈ oddS σ)
    (hrest : ∀ r ∈ oddS σ, r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = e ∨ r = f ∨ r = g ∨ r = h ∨
      h < r) :
    syll σ = Gen.k a b c d h1 h2 h3 :: signs σ [a, b, c, d] ∧
    syll (next σ) = Gen.k e f g h h5 h6 h7 :: signs σ [e, f, g, h] ∧
    next σ ≠ 1 ∧
    ∃ u2 : Fin n → ℤ, IsCol (wact (syll (next σ) ++ syll σ) (pcol σ)) (lde σ) u2 ∧
      u2 a = (fix4 (wint σ a) + fix4 (wint σ b) + fix4 (wint σ c) + fix4 (wint σ d)) / 2 ∧
      u2 b = (fix4 (wint σ a) - fix4 (wint σ b) + fix4 (wint σ c) - fix4 (wint σ d)) / 2 ∧
      u2 c = (fix4 (wint σ a) + fix4 (wint σ b) - fix4 (wint σ c) - fix4 (wint σ d)) / 2 ∧
      u2 d = (fix4 (wint σ a) - fix4 (wint σ b) - fix4 (wint σ c) + fix4 (wint σ d)) / 2 ∧
      u2 e = (fix4 (wint σ e) + fix4 (wint σ f) + fix4 (wint σ g) + fix4 (wint σ h)) / 2 ∧
      u2 f = (fix4 (wint σ e) - fix4 (wint σ f) + fix4 (wint σ g) - fix4 (wint σ h)) / 2 ∧
      u2 g = (fix4 (wint σ e) + fix4 (wint σ f) - fix4 (wint σ g) - fix4 (wint σ h)) / 2 ∧
      u2 h = (fix4 (wint σ e) - fix4 (wint σ f) - fix4 (wint σ g) + fix4 (wint σ h)) / 2 ∧
      ∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ e → r ≠ f → r ≠ g → r ≠ h →
        u2 r = wint σ r := by
  have hU := pivot_pos hσ
  have v1 := Fin.lt_def.1 h1; have v2 := Fin.lt_def.1 h2; have v3 := Fin.lt_def.1 h3
  have v4 := Fin.lt_def.1 h4; have v5 := Fin.lt_def.1 h5; have v6 := Fin.lt_def.1 h6
  have v7 := Fin.lt_def.1 h7
  have ne : ∀ {x y : Fin n}, x.val < y.val → y ≠ x := fun hxy e => by subst e; omega
  have ne' : ∀ {x y : Fin n}, x.val < y.val → x ≠ y := fun hxy e => by subst e; omega
  have hrest4 : ∀ r ∈ oddS σ, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r := by
    intro r hr
    rcases hrest r hr with e' | e' | e' | e' | e' | e' | e' | e' | e'
    · exact Or.inl e'
    · exact Or.inr (Or.inl e')
    · exact Or.inr (Or.inr (Or.inl e'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e')))
    all_goals (right; right; right; right)
    · rw [e']; exact h4
    · rw [e']; exact h4.trans h5
    · rw [e']; exact h4.trans (h5.trans h6)
    · rw [e']; exact h4.trans (h5.trans (h6.trans h7))
    · exact h4.trans (h5.trans (h6.trans (h7.trans e')))
  obtain ⟨hs1, u1, c1, va, vb, vc, vd, o1⟩ := isCol_syll hσ hk h1 h2 h3 ha hb hc hd hrest4
  have hF : ∀ x ∈ oddS σ, fix4 (wint σ x) % 4 = 1 := fun x hx => fix4_mod ((mem_oddS_iff x).1 hx)
  have pa := hF a ha; have pb := hF b hb; have pc := hF c hc; have pd := hF d hd
  have ue : u1 e = wint σ e := o1 e (ne (by omega)) (ne (by omega)) (ne (by omega)) (ne (by omega))
  have oe : Odd (u1 e) := by rw [ue]; exact (mem_oddS_iff e).1 he
  have hdJ : d.val < pivotJ σ := le_pidx_of_odd hσ hd
  have hl1 : BelowJ (pivotJ σ) (syll σ) := by
    rw [hs1]; intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hdJ
    · exact signs_extent (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> omega) x hx
  obtain ⟨hp1, hcol1⟩ := pcol_word σ hU (syll σ) hl1 (not_unit_of_odd c1 hk oe _)
  have hk1 : lde (next σ) = lde σ := lde_eq (k := lde σ) (by rw [next, hcol1]; exact c1) hk ⟨e, oe⟩
  have c1' : IsCol (pcol (next σ)) (lde (next σ)) u1 := by rw [hk1, next, hcol1]; exact c1
  have hw1 : ∀ r, wint (next σ) r = u1 r := wint_eq c1'
  have hne1 : next σ ≠ 1 := by
    intro e1; have := pivot_pos hσ
    have h0 := hp1
    rw [show FreeMonoid.lift (sem n) (FreeMonoid.ofList (syll σ)) * σ = next σ from rfl, e1,
      (pivotJ_eq_zero_iff 1).2 rfl] at h0
    omega
  have hmem1 : ∀ r, r ∈ oddS (next σ) ↔ Odd (u1 r) := fun r => by rw [mem_oddS_iff, hw1]
  have oo : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → (x ∈ oddS (next σ) ↔ x ∈ oddS σ) := by
    intro x e0 e1 e2 e3; rw [hmem1, o1 x e0 e1 e2 e3, mem_oddS_iff]
  have he1 := (oo e (ne (by omega)) (ne (by omega)) (ne (by omega)) (ne (by omega))).2 he
  have hf1 := (oo f (ne (by omega)) (ne (by omega)) (ne (by omega)) (ne (by omega))).2 hf
  have hg1 := (oo g (ne (by omega)) (ne (by omega)) (ne (by omega)) (ne (by omega))).2 hg
  have hh1 := (oo h (ne (by omega)) (ne (by omega)) (ne (by omega)) (ne (by omega))).2 hh
  have ev1 : ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) → ¬ Odd (u1 x) := by
    intro x hx ho
    have := Int.odd_iff.1 ho
    rcases hx with rfl | rfl | rfl | rfl
    · rw [va] at this; omega
    · rw [vb] at this; omega
    · rw [vc] at this; omega
    · rw [vd] at this; omega
  have hrest1 : ∀ r ∈ oddS (next σ), r = e ∨ r = f ∨ r = g ∨ r = h ∨ h < r := by
    intro r hr
    have hr' := (hmem1 r).1 hr
    by_cases e0 : r = a; · exact absurd hr' (ev1 r (Or.inl e0))
    by_cases e1 : r = b; · exact absurd hr' (ev1 r (Or.inr (Or.inl e1)))
    by_cases e2 : r = c; · exact absurd hr' (ev1 r (Or.inr (Or.inr (Or.inl e2))))
    by_cases e3 : r = d; · exact absurd hr' (ev1 r (Or.inr (Or.inr (Or.inr e3))))
    rcases hrest r ((oo r e0 e1 e2 e3).1 hr) with x | x | x | x | x | x | x | x | x
    · exact absurd x e0
    · exact absurd x e1
    · exact absurd x e2
    · exact absurd x e3
    · exact Or.inl x
    · exact Or.inr (Or.inl x)
    · exact Or.inr (Or.inr (Or.inl x))
    · exact Or.inr (Or.inr (Or.inr (Or.inl x)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr x)))
  obtain ⟨hs2, u2, c2, ve, vf, vg, vh, o2⟩ :=
    isCol_syll hne1 (by rw [hk1]; exact hk) h5 h6 h7 he1 hf1 hg1 hh1 hrest1
  have hsg : signs (next σ) [e, f, g, h] = signs σ [e, f, g, h] := signs_congr σ (next σ) _ (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hw1]
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact o1 _ (ne (by omega)) (ne (by omega)) (ne (by omega)) (ne (by omega)))
  have wE : ∀ x, x = e ∨ x = f ∨ x = g ∨ x = h → wint (next σ) x = wint σ x := by
    intro x hx; rw [hw1]
    rcases hx with rfl | rfl | rfl | rfl <;>
      exact o1 _ (ne (by omega)) (ne (by omega)) (ne (by omega)) (ne (by omega))
  rw [wE e (Or.inl rfl), wE f (Or.inr (Or.inl rfl)), wE g (Or.inr (Or.inr (Or.inl rfl))),
    wE h (Or.inr (Or.inr (Or.inr rfl)))] at ve vf vg vh
  refine ⟨hs1, by rw [hs2, hsg], hne1, u2, ?_, ?_, ?_, ?_, ?_, ve, vf, vg, vh, ?_⟩
  · rw [wact_append, ← hcol1, ← hk1]
    exact c2
  · rw [o2 a (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), hw1, va]
  · rw [o2 b (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), hw1, vb]
  · rw [o2 c (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), hw1, vc]
  · rw [o2 d (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), hw1, vd]
  · intro r e0 e1 e2 e3 e4 e5 e6 e7
    rw [o2 r e4 e5 e6 e7, hw1, o1 r e0 e1 e2 e3]

/-- The states along `T = K_[e,f,g,h] K_[a,b,c,d] (−1)_[a] (−1)_[e] X_[a,e]` after
the two syllables lie below the level (sum `≡ 4 (mod 8)`). -/
theorem eight_lev_e {σ : O_ZHalf n} (hσ : σ ≠ 1) (hk : 0 < lde σ) {a b c d e f g h : Fin n}
    (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) (h5 : e < f) (h6 : f < g) (h7 : g < h)
    (ha : a ∈ oddS σ) (hb : b ∈ oddS σ) (hc : c ∈ oddS σ) (hd : d ∈ oddS σ)
    (he : e ∈ oddS σ) (hf : f ∈ oddS σ) (hg : g ∈ oddS σ) (hh : h ∈ oddS σ)
    (hrest : ∀ r ∈ oddS σ, r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = e ∨ r = f ∨ r = g ∨ r = h ∨
      h < r)
    (hsum : (fix4 (wint σ a) + fix4 (wint σ b) + fix4 (wint σ c) + fix4 (wint σ d) +
      fix4 (wint σ e) + fix4 (wint σ f) + fix4 (wint σ g) + fix4 (wint σ h)) % 8 = 4) :
    ∀ j ≤ 5, level (FreeMonoid.lift (sem n) (FreeMonoid.ofList
      ([Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg e,
        Gen.x a e (h1.trans (h2.trans (h3.trans h4)))].drop j)) * next (next σ)) < level σ := by
  have v1 := Fin.lt_def.1 h1; have v2 := Fin.lt_def.1 h2; have v3 := Fin.lt_def.1 h3
  have v4 := Fin.lt_def.1 h4; have v5 := Fin.lt_def.1 h5; have v6 := Fin.lt_def.1 h6
  have v7 := Fin.lt_def.1 h7
  have ne : ∀ {x y : Fin n}, x.val < y.val → y ≠ x := fun hxy e => by subst e; omega
  have ne' : ∀ {x y : Fin n}, x.val < y.val → x ≠ y := fun hxy e => by subst e; omega
  obtain ⟨hs1, hs2, hne1, u2, c2, va, vb, vc, vd, ve, vf, vg, vh, o2⟩ :=
    eight_syll hσ hk h1 h2 h3 h4 h5 h6 h7 ha hb hc hd he hf hg hh hrest
  have hF : ∀ x ∈ oddS σ, fix4 (wint σ x) % 4 = 1 := fun x hx => fix4_mod ((mem_oddS_iff x).1 hx)
  obtain ⟨ea, eb, ec, ed, ee, ef, eg, eh, k1, k1a, k1b, k1c, k1d, k2, k2e, k2f, k2g, k2h⟩ :=
    par8_e _ _ _ _ _ _ _ _ (hF a ha) (hF b hb) (hF c hc) (hF d hd) (hF e he) (hF f hf)
      (hF g hg) (hF h hh) hsum _ _ _ _ _ _ _ _ va vb vc vd ve vf vg vh
  have hJ : h.val < pivotJ σ := le_pidx_of_odd hσ hh
  have hνF : FixCols (mat (next (next σ))) (pivotJ σ) := fixCols_iterN 2 σ (fixCols_pivotJ σ)
  have hνL : level (next (next σ)) < level σ :=
    lt_of_le_of_lt (level_next_le _) (level_next_lt σ hσ)
  obtain ⟨u3, c3, x3a, x3z, o3⟩ := step_x c2 (h1.trans (h2.trans (h3.trans h4)))
  obtain ⟨u4, c4, x4z, o4⟩ := step_neg c3 e
  obtain ⟨u5, c5, x5a, o5⟩ := step_neg c4 a
  have w5a : u5 a = -u2 e := by rw [x5a, o4 a (ne' (by omega)), x3a]
  have w5z : u5 e = -u2 a := by rw [o5 e (ne (by omega)), x4z, x3z]
  have w5 : ∀ r, r ≠ a → r ≠ e → u5 r = u2 r := fun r ra rz => by
    rw [o5 r ra, o4 r rz, o3 r ra rz]
  have hstate : ∀ l : List (Gen n), FreeMonoid.lift (sem n) (FreeMonoid.ofList
      (l ++ (syll (next σ) ++ syll σ))) * σ =
      FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * next (next σ) := by
    intro l
    simp only [FreeMonoid.ofList_append, map_mul, mul_assoc]
    rfl
  have hbelow : ∀ l : List (Gen n), (∀ x ∈ l, extent x ≤ h.val) →
      BelowJ (pivotJ σ) (l ++ (syll (next σ) ++ syll σ)) := by
    intro l hl x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact lt_of_le_of_lt (hl x hx) hJ
    rcases List.mem_append.1 hx with hx | hx
    · rw [hs2] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hJ
      · exact signs_extent (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> omega) x hx
    · rw [hs1] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · show d.val < pivotJ σ; omega
      · exact signs_extent (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> omega) x hx
  have hoa : Odd (wint σ a) := (mem_oddS_iff a).1 ha
  obtain ⟨u6, c6, y6a, y6b, y6c, y6d, o6⟩ := step_k c5 h1 h2 h3 (by
    rw [w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))]; exact k1)
  have w6 : ∀ r, r = e ∨ r = f ∨ r = g ∨ r = h → u6 r = u5 r := fun r hr => by
    apply o6 <;> rcases hr with rfl | rfl | rfl | rfl <;> exact ne (by omega)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
  · obtain ⟨u7, c7, y7e, y7f, y7g, y7h, o7⟩ := step_k c6 h5 h6 h7 (by
      rw [w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5z, w5 f (ne (by omega)) (ne (by omega)), w5 g (ne (by omega)) (ne (by omega)), w5 h (ne (by omega)) (ne (by omega))]
      exact k2)
    have hl := hbelow [Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg e,
      Gen.x a e (h1.trans (h2.trans (h3.trans h4)))] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [extent] <;> omega)
    have := level_lt_of_col hσ hk _ hl (u' := u7)
      (by rw [wact_append]; exact c7) (fun r hr => by
        have ho := Int.odd_iff.1 hr
        by_cases ra : r = a
        · rw [ra, o7 a (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6a, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rb : r = b
        · rw [rb, o7 b (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6b, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rc : r = c
        · rw [rc, o7 c (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6c, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rd : r = d
        · rw [rd, o7 d (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6d, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases re : r = e
        · rw [re, y7e, w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5z, w5 f (ne (by omega)) (ne (by omega)), w5 g (ne (by omega)) (ne (by omega)), w5 h (ne (by omega)) (ne (by omega))] at ho; exfalso; omega
        by_cases rf : r = f
        · rw [rf, y7f, w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5z, w5 f (ne (by omega)) (ne (by omega)), w5 g (ne (by omega)) (ne (by omega)), w5 h (ne (by omega)) (ne (by omega))] at ho; exfalso; omega
        by_cases rg : r = g
        · rw [rg, y7g, w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5z, w5 f (ne (by omega)) (ne (by omega)), w5 g (ne (by omega)) (ne (by omega)), w5 h (ne (by omega)) (ne (by omega))] at ho; exfalso; omega
        by_cases rh : r = h
        · rw [rh, y7h, w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5z, w5 f (ne (by omega)) (ne (by omega)), w5 g (ne (by omega)) (ne (by omega)), w5 h (ne (by omega)) (ne (by omega))] at ho; exfalso; omega
        rw [o7 r re rf rg rh, o6 r ra rb rc rd, w5 r ra re,
          o2 r ra rb rc rd re rf rg rh] at hr
        exact hr) (r₀ := a) hoa (fun hr => by
          have ho := Int.odd_iff.1 hr
          rw [o7 a (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6a, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; omega)
    rwa [hstate] at this
  · have hl := hbelow [Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg e, Gen.x a e (h1.trans (h2.trans (h3.trans h4)))] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [extent] <;> omega)
    have := level_lt_of_col hσ hk _ hl (u' := u6)
      (by rw [wact_append]; exact c6) (fun r hr => by
        have ho := Int.odd_iff.1 hr
        by_cases ra : r = a
        · rw [ra, y6a, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rb : r = b
        · rw [rb, y6b, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rc : r = c
        · rw [rc, y6c, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rd : r = d
        · rw [rd, y6d, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        rw [o6 r ra rb rc rd] at ho hr
        by_cases re : r = e
        · rw [re, w5z] at ho; exfalso; omega
        rw [w5 r ra re] at ho hr
        by_cases rf : r = f
        · rw [rf] at ho; exfalso; omega
        by_cases rg : r = g
        · rw [rg] at ho; exfalso; omega
        by_cases rh : r = h
        · rw [rh] at ho; exfalso; omega
        rwa [o2 r ra rb rc rd re rf rg rh] at hr) (r₀ := a) hoa (fun hr => by
          have ho := Int.odd_iff.1 hr
          rw [y6a, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; omega)
    rwa [hstate] at this
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    have e2 : ([Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg e,
        Gen.x a e (h1.trans (h2.trans (h3.trans h4)))].drop (i + 2)) = [Gen.neg a, Gen.neg e, Gen.x a e (h1.trans (h2.trans (h3.trans h4)))].drop i := rfl
    rw [e2]
    refine (level_sp_word hσ hk _ (fun x hx => ?_) hνF hνL).2
    have hx' := List.mem_of_mem_drop hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl <;> exact ⟨by simp [Gen.tag], by simp [extent]; omega⟩

/-- The states along `T = K_[e,f,g,h] K_[a,b,c,d] (−1)_[a] (−1)_[h] X_[a,h]` after
the two syllables lie below the level (sum `≡ 0 (mod 8)`). -/
theorem eight_lev_h {σ : O_ZHalf n} (hσ : σ ≠ 1) (hk : 0 < lde σ) {a b c d e f g h : Fin n}
    (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) (h5 : e < f) (h6 : f < g) (h7 : g < h)
    (ha : a ∈ oddS σ) (hb : b ∈ oddS σ) (hc : c ∈ oddS σ) (hd : d ∈ oddS σ)
    (he : e ∈ oddS σ) (hf : f ∈ oddS σ) (hg : g ∈ oddS σ) (hh : h ∈ oddS σ)
    (hrest : ∀ r ∈ oddS σ, r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = e ∨ r = f ∨ r = g ∨ r = h ∨
      h < r)
    (hsum : (fix4 (wint σ a) + fix4 (wint σ b) + fix4 (wint σ c) + fix4 (wint σ d) +
      fix4 (wint σ e) + fix4 (wint σ f) + fix4 (wint σ g) + fix4 (wint σ h)) % 8 = 0) :
    ∀ j ≤ 5, level (FreeMonoid.lift (sem n) (FreeMonoid.ofList
      ([Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg h,
        Gen.x a h (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))].drop j)) * next (next σ)) < level σ := by
  have v1 := Fin.lt_def.1 h1; have v2 := Fin.lt_def.1 h2; have v3 := Fin.lt_def.1 h3
  have v4 := Fin.lt_def.1 h4; have v5 := Fin.lt_def.1 h5; have v6 := Fin.lt_def.1 h6
  have v7 := Fin.lt_def.1 h7
  have ne : ∀ {x y : Fin n}, x.val < y.val → y ≠ x := fun hxy e => by subst e; omega
  have ne' : ∀ {x y : Fin n}, x.val < y.val → x ≠ y := fun hxy e => by subst e; omega
  obtain ⟨hs1, hs2, hne1, u2, c2, va, vb, vc, vd, ve, vf, vg, vh, o2⟩ :=
    eight_syll hσ hk h1 h2 h3 h4 h5 h6 h7 ha hb hc hd he hf hg hh hrest
  have hF : ∀ x ∈ oddS σ, fix4 (wint σ x) % 4 = 1 := fun x hx => fix4_mod ((mem_oddS_iff x).1 hx)
  obtain ⟨ea, eb, ec, ed, ee, ef, eg, eh, k1, k1a, k1b, k1c, k1d, k2, k2e, k2f, k2g, k2h⟩ :=
    par8_h _ _ _ _ _ _ _ _ (hF a ha) (hF b hb) (hF c hc) (hF d hd) (hF e he) (hF f hf)
      (hF g hg) (hF h hh) hsum _ _ _ _ _ _ _ _ va vb vc vd ve vf vg vh
  have hJ : h.val < pivotJ σ := le_pidx_of_odd hσ hh
  have hνF : FixCols (mat (next (next σ))) (pivotJ σ) := fixCols_iterN 2 σ (fixCols_pivotJ σ)
  have hνL : level (next (next σ)) < level σ :=
    lt_of_le_of_lt (level_next_le _) (level_next_lt σ hσ)
  obtain ⟨u3, c3, x3a, x3z, o3⟩ := step_x c2 (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))
  obtain ⟨u4, c4, x4z, o4⟩ := step_neg c3 h
  obtain ⟨u5, c5, x5a, o5⟩ := step_neg c4 a
  have w5a : u5 a = -u2 h := by rw [x5a, o4 a (ne' (by omega)), x3a]
  have w5z : u5 h = -u2 a := by rw [o5 h (ne (by omega)), x4z, x3z]
  have w5 : ∀ r, r ≠ a → r ≠ h → u5 r = u2 r := fun r ra rz => by
    rw [o5 r ra, o4 r rz, o3 r ra rz]
  have hstate : ∀ l : List (Gen n), FreeMonoid.lift (sem n) (FreeMonoid.ofList
      (l ++ (syll (next σ) ++ syll σ))) * σ =
      FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * next (next σ) := by
    intro l
    simp only [FreeMonoid.ofList_append, map_mul, mul_assoc]
    rfl
  have hbelow : ∀ l : List (Gen n), (∀ x ∈ l, extent x ≤ h.val) →
      BelowJ (pivotJ σ) (l ++ (syll (next σ) ++ syll σ)) := by
    intro l hl x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact lt_of_le_of_lt (hl x hx) hJ
    rcases List.mem_append.1 hx with hx | hx
    · rw [hs2] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hJ
      · exact signs_extent (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> omega) x hx
    · rw [hs1] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · show d.val < pivotJ σ; omega
      · exact signs_extent (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> omega) x hx
  have hoa : Odd (wint σ a) := (mem_oddS_iff a).1 ha
  obtain ⟨u6, c6, y6a, y6b, y6c, y6d, o6⟩ := step_k c5 h1 h2 h3 (by
    rw [w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))]; exact k1)
  have w6 : ∀ r, r = e ∨ r = f ∨ r = g ∨ r = h → u6 r = u5 r := fun r hr => by
    apply o6 <;> rcases hr with rfl | rfl | rfl | rfl <;> exact ne (by omega)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
  · obtain ⟨u7, c7, y7e, y7f, y7g, y7h, o7⟩ := step_k c6 h5 h6 h7 (by
      rw [w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5 e (ne (by omega)) (ne' (by omega)), w5 f (ne (by omega)) (ne' (by omega)), w5 g (ne (by omega)) (ne' (by omega)), w5z]
      exact k2)
    have hl := hbelow [Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg h,
      Gen.x a h (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [extent] <;> omega)
    have := level_lt_of_col hσ hk _ hl (u' := u7)
      (by rw [wact_append]; exact c7) (fun r hr => by
        have ho := Int.odd_iff.1 hr
        by_cases ra : r = a
        · rw [ra, o7 a (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6a, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rb : r = b
        · rw [rb, o7 b (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6b, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rc : r = c
        · rw [rc, o7 c (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6c, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rd : r = d
        · rw [rd, o7 d (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6d, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases re : r = e
        · rw [re, y7e, w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5 e (ne (by omega)) (ne' (by omega)), w5 f (ne (by omega)) (ne' (by omega)), w5 g (ne (by omega)) (ne' (by omega)), w5z] at ho; exfalso; omega
        by_cases rf : r = f
        · rw [rf, y7f, w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5 e (ne (by omega)) (ne' (by omega)), w5 f (ne (by omega)) (ne' (by omega)), w5 g (ne (by omega)) (ne' (by omega)), w5z] at ho; exfalso; omega
        by_cases rg : r = g
        · rw [rg, y7g, w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5 e (ne (by omega)) (ne' (by omega)), w5 f (ne (by omega)) (ne' (by omega)), w5 g (ne (by omega)) (ne' (by omega)), w5z] at ho; exfalso; omega
        by_cases rh : r = h
        · rw [rh, y7h, w6 e (by simp), w6 f (by simp), w6 g (by simp), w6 h (by simp), w5 e (ne (by omega)) (ne' (by omega)), w5 f (ne (by omega)) (ne' (by omega)), w5 g (ne (by omega)) (ne' (by omega)), w5z] at ho; exfalso; omega
        rw [o7 r re rf rg rh, o6 r ra rb rc rd, w5 r ra rh,
          o2 r ra rb rc rd re rf rg rh] at hr
        exact hr) (r₀ := a) hoa (fun hr => by
          have ho := Int.odd_iff.1 hr
          rw [o7 a (ne' (by omega)) (ne' (by omega)) (ne' (by omega)) (ne' (by omega)), y6a, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; omega)
    rwa [hstate] at this
  · have hl := hbelow [Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg h, Gen.x a h (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [extent] <;> omega)
    have := level_lt_of_col hσ hk _ hl (u' := u6)
      (by rw [wact_append]; exact c6) (fun r hr => by
        have ho := Int.odd_iff.1 hr
        by_cases ra : r = a
        · rw [ra, y6a, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rb : r = b
        · rw [rb, y6b, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rc : r = c
        · rw [rc, y6c, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        by_cases rd : r = d
        · rw [rd, y6d, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; exfalso; omega
        rw [o6 r ra rb rc rd] at ho hr
        by_cases rh : r = h
        · rw [rh, w5z] at ho; exfalso; omega
        rw [w5 r ra rh] at ho hr
        by_cases re : r = e
        · rw [re] at ho; exfalso; omega
        by_cases rf : r = f
        · rw [rf] at ho; exfalso; omega
        by_cases rg : r = g
        · rw [rg] at ho; exfalso; omega
        rwa [o2 r ra rb rc rd re rf rg rh] at hr) (r₀ := a) hoa (fun hr => by
          have ho := Int.odd_iff.1 hr
          rw [y6a, w5a, w5 b (ne (by omega)) (ne' (by omega)), w5 c (ne (by omega)) (ne' (by omega)), w5 d (ne (by omega)) (ne' (by omega))] at ho; omega)
    rwa [hstate] at this
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    have e2 : ([Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg h,
        Gen.x a h (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))].drop (i + 2)) = [Gen.neg a, Gen.neg h, Gen.x a h (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))].drop i := rfl
    rw [e2]
    refine (level_sp_word hσ hk _ (fun x hx => ?_) hνF hνL).2
    have hx' := List.mem_of_mem_drop hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl <;> exact ⟨by simp [Gen.tag], by simp [extent]; omega⟩

/-! ## The derivation: the signs move across, `W⁻¹ C W ≈ C` does the rest -/

/-- Words of sign letters commute. -/
theorem signs_comm {l₁ l₂ : List (Gen n)} (h₁ : ∀ x ∈ l₁, ∃ r, x = Gen.neg r)
    (h₂ : ∀ x ∈ l₂, ∃ r, x = Gen.neg r) :
    Derivable (Table1 n) (FreeMonoid.ofList l₁ * FreeMonoid.ofList l₂)
      (FreeMonoid.ofList l₂ * FreeMonoid.ofList l₁) :=
  comm_list (fun x hx => by
    obtain ⟨r, rfl⟩ := h₁ x hx
    exact (comm_list (fun x' hx' => by
      obtain ⟨r', rfl⟩ := h₂ x' hx'
      exact neg_comm r' r)).symm)

theorem negw_neg (t : Bool) (x : Fin n) : ∀ y ∈ negw t x, ∃ r, y = Gen.neg r := by
  intro y hy; cases t <;> simp [negw] at hy; exact ⟨x, hy⟩

theorem negw_mem (t : Bool) (x : Fin n) : ∀ y ∈ negw t x, ∃ r, y = Gen.neg r ∧ r = x := by
  intro y hy; cases t <;> simp [negw] at hy; exact ⟨x, hy, rfl⟩

/-- A sign word away from `K`'s indices commutes with `K`. -/
theorem signs_k_comm {l : List (Gen n)} {a b c d : Fin n} (h₁ : a < b) (h₂ : b < c) (h₃ : c < d)
    (hl : ∀ x ∈ l, ∃ r, x = Gen.neg r ∧ [r, a, b, c, d].Nodup) :
    Derivable (Table1 n) (FreeMonoid.ofList l * FreeMonoid.of (Gen.k a b c d h₁ h₂ h₃))
      (FreeMonoid.of (Gen.k a b c d h₁ h₂ h₃) * FreeMonoid.ofList l) :=
  comm_list (fun x hx => by
    obtain ⟨r, rfl, hr⟩ := hl x hx
    exact Derivable.of (Table1.r2e r a b c d h₁ h₂ h₃ hr))

/-- A sign word away from `x, y` commutes with `X_[x,y]`. -/
theorem signs_x_comm {l : List (Gen n)} {x y : Fin n} (hxy : x < y)
    (hl : ∀ z ∈ l, ∃ r, z = Gen.neg r ∧ [x, y, r].Nodup) :
    Derivable (Table1 n) (FreeMonoid.of (Gen.x x y hxy) * FreeMonoid.ofList l)
      (FreeMonoid.ofList l * FreeMonoid.of (Gen.x x y hxy)) :=
  (comm_list (fun z hz => by
    obtain ⟨r, rfl, hr⟩ := hl z hz
    exact (Derivable.of (Table1.r2b x y r hxy hr)).symm)).symm

/-- The square of Subcase 1.2.2.3 with `u_e` odd, given `P ≈ C`: the signs of
`d` and `e` exchange across `X_[d,e]`, the others commute through. -/
theorem der1223 {a b c d e f g h : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e)
    (h5 : e < f) (h6 : f < g) (h7 : g < h) (Pfix : List (Gen n))
    (hP : Derivable (Table1 n) (FreeMonoid.ofList Pfix)
      (FreeMonoid.ofList [Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.x d e h4,
        Gen.k a b c d h1 h2 h3, Gen.k e f g h h5 h6 h7]))
    (A F : List (Gen n)) (hA : ∀ x ∈ A, ∃ r, x = Gen.neg r ∧ r.val < d.val)
    (hF : ∀ x ∈ F, ∃ r, x = Gen.neg r ∧ e.val < r.val) (td te : Bool) :
    Derivable (Table1 n)
      (FreeMonoid.ofList ((Gen.k e f g h h5 h6 h7 :: (negw td e ++ F)) ++
        (Gen.k a b c d h1 h2 h3 :: (A ++ negw te d))) * FreeMonoid.of (Gen.x d e h4))
      (FreeMonoid.ofList (Pfix ++ (Gen.k e f g h h5 h6 h7 :: (negw te e ++ F))) *
        FreeMonoid.ofList (Gen.k a b c d h1 h2 h3 :: (A ++ negw td d))) := by
  have v1 := Fin.lt_def.1 h1; have v2 := Fin.lt_def.1 h2; have v3 := Fin.lt_def.1 h3
  have v4 := Fin.lt_def.1 h4; have v5 := Fin.lt_def.1 h5; have v6 := Fin.lt_def.1 h6
  have v7 := Fin.lt_def.1 h7
  have sA : ∀ x ∈ A, ∃ r, x = Gen.neg r := fun x hx => (hA x hx).imp fun r h => h.1
  have sF : ∀ x ∈ F, ∃ r, x = Gen.neg r := fun x hx => (hF x hx).imp fun r h => h.1
  -- `K_[a,b,c,d]` commutes with the signs on `e, …, h`
  have kE : ∀ t : Bool, Derivable (Table1 n) (FreeMonoid.ofList (negw t e ++ F))
      (FreeMonoid.of (Gen.k a b c d h1 h2 h3) * FreeMonoid.ofList (negw t e ++ F) *
        FreeMonoid.of (Gen.k a b c d h1 h2 h3)) := by
    intro t
    have hc := signs_k_comm h1 h2 h3 (l := negw t e ++ F) (fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨r, rfl, rfl⟩ := negw_mem t e x hx
        exact ⟨r, rfl, nodup_vals (by simp; omega)⟩
      · obtain ⟨r, rfl, hr⟩ := hF x hx
        exact ⟨r, rfl, nodup_vals (by simp; omega)⟩)
    have e1 : Derivable (Table1 n) (FreeMonoid.ofList (negw t e ++ F))
        (FreeMonoid.ofList (negw t e ++ F) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
          FreeMonoid.of (Gen.k a b c d h1 h2 h3)) := by
      have := (Derivable.refl (FreeMonoid.ofList (negw t e ++ F))).mul
        (sq_derivable (Gen.k a b c d h1 h2 h3)).symm
      simpa [mul_assoc] using this
    exact e1.trans (hc.mul (Derivable.refl _))
  -- the right-hand side
  have r1 : Derivable (Table1 n)
      (FreeMonoid.ofList (Pfix ++ (Gen.k e f g h h5 h6 h7 :: (negw te e ++ F))) *
        FreeMonoid.ofList (Gen.k a b c d h1 h2 h3 :: (A ++ negw td d)))
      (FreeMonoid.of (Gen.k e f g h h5 h6 h7) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
        FreeMonoid.of (Gen.x d e h4) * FreeMonoid.ofList (negw te e ++ F) *
        FreeMonoid.ofList A * FreeMonoid.ofList (negw td d)) := by
    have s1 := (hP.mul (Derivable.refl (FreeMonoid.ofList
      (Gen.k e f g h h5 h6 h7 :: (negw te e ++ F))))).mul
      (Derivable.refl (FreeMonoid.ofList (Gen.k a b c d h1 h2 h3 :: (A ++ negw td d))))
    refine (deq ?_).trans (s1.trans ?_)
    · simp [FreeMonoid.ofList_append, mul_assoc]
    have q1 : FreeMonoid.ofList [Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.x d e h4,
          Gen.k a b c d h1 h2 h3, Gen.k e f g h h5 h6 h7] *
        FreeMonoid.ofList (Gen.k e f g h h5 h6 h7 :: (negw te e ++ F)) *
        FreeMonoid.ofList (Gen.k a b c d h1 h2 h3 :: (A ++ negw td d)) =
        FreeMonoid.of (Gen.k e f g h h5 h6 h7) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
          FreeMonoid.of (Gen.x d e h4) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
          (FreeMonoid.of (Gen.k e f g h h5 h6 h7) * FreeMonoid.of (Gen.k e f g h h5 h6 h7)) *
          FreeMonoid.ofList (negw te e ++ F) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
          FreeMonoid.ofList A * FreeMonoid.ofList (negw td d) := by
      simp [FreeMonoid.ofList_append, mul_assoc]
    rw [q1]
    refine (((((((Derivable.refl _).mul (sq_derivable (Gen.k e f g h h5 h6 h7))).mul
      (Derivable.refl _)).mul (Derivable.refl _)).mul (Derivable.refl _)).mul
      (Derivable.refl _))).trans ?_
    have q2 : FreeMonoid.of (Gen.k e f g h h5 h6 h7) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
          FreeMonoid.of (Gen.x d e h4) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) * 1 *
          FreeMonoid.ofList (negw te e ++ F) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
          FreeMonoid.ofList A * FreeMonoid.ofList (negw td d) =
        FreeMonoid.of (Gen.k e f g h h5 h6 h7) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
          FreeMonoid.of (Gen.x d e h4) *
          (FreeMonoid.of (Gen.k a b c d h1 h2 h3) * FreeMonoid.ofList (negw te e ++ F) *
            FreeMonoid.of (Gen.k a b c d h1 h2 h3)) *
          FreeMonoid.ofList A * FreeMonoid.ofList (negw td d) := by
      simp only [mul_one, mul_assoc]
    rw [q2]
    exact (((Derivable.refl _).mul (kE te).symm).mul (Derivable.refl _)).mul (Derivable.refl _)
  -- `X_[d,e]` across the signs
  have r2 : Derivable (Table1 n)
      (FreeMonoid.of (Gen.x d e h4) * FreeMonoid.ofList (negw te e ++ F) *
        FreeMonoid.ofList A * FreeMonoid.ofList (negw td d))
      (FreeMonoid.ofList (negw te d) * FreeMonoid.ofList (F ++ A) *
        FreeMonoid.ofList (negw td e) * FreeMonoid.of (Gen.x d e h4)) := by
    have xFA := signs_x_comm h4 (l := F ++ A) (fun z hz => by
      rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨r, rfl, hr⟩ := hF z hz; exact ⟨r, rfl, nodup_vals (by simp; omega)⟩
      · obtain ⟨r, rfl, hr⟩ := hA z hz; exact ⟨r, rfl, nodup_vals (by simp; omega)⟩)
    have w1 := (negw_swap' h4 te).symm
    have w2 := (negw_swap h4 td).symm
    have e1 : FreeMonoid.of (Gen.x d e h4) * FreeMonoid.ofList (negw te e ++ F) *
        FreeMonoid.ofList A * FreeMonoid.ofList (negw td d) =
        (FreeMonoid.of (Gen.x d e h4) * FreeMonoid.ofList (negw te e)) *
          FreeMonoid.ofList (F ++ A) * FreeMonoid.ofList (negw td d) := by
      simp [FreeMonoid.ofList_append, mul_assoc]
    rw [e1]
    refine ((w1.mul (Derivable.refl _)).mul (Derivable.refl _)).trans ?_
    have s5 := (Derivable.refl (FreeMonoid.ofList (negw te d))).mul
      ((xFA.mul (Derivable.refl (FreeMonoid.ofList (negw td d)))).trans
        ((deq (mul_assoc _ _ _)).trans
          ((Derivable.refl (FreeMonoid.ofList (F ++ A))).mul w2)))
    exact (deq (by simp only [mul_assoc])).trans (s5.trans (deq (by simp only [mul_assoc])))
  -- the signs of `d` and `e` exchange places
  have r3 : Derivable (Table1 n)
      (FreeMonoid.ofList (negw te d) * FreeMonoid.ofList (F ++ A) * FreeMonoid.ofList (negw td e))
      (FreeMonoid.ofList (negw td e) * FreeMonoid.ofList (F ++ A) * FreeMonoid.ofList (negw te d)) := by
    have hFA : ∀ x ∈ F ++ A, ∃ r, x = Gen.neg r := fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact sF x hx
      · exact sA x hx
    have sc := signs_comm (negw_neg te d) (l₂ := F ++ A ++ negw td e) (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hFA x hx
        · exact negw_neg td e x hx)
    have sc2 := signs_comm hFA (negw_neg td e)
    refine (deq (by simp only [FreeMonoid.ofList_append, mul_assoc])).trans (sc.trans ?_)
    refine (deq (by simp only [FreeMonoid.ofList_append, mul_assoc])).trans
      ((sc2.mul (Derivable.refl (FreeMonoid.ofList (negw te d)))).trans (deq (by simp only [FreeMonoid.ofList_append, mul_assoc])))
  -- the left-hand side
  have r4 : Derivable (Table1 n)
      (FreeMonoid.ofList ((Gen.k e f g h h5 h6 h7 :: (negw td e ++ F)) ++
        (Gen.k a b c d h1 h2 h3 :: (A ++ negw te d))) * FreeMonoid.of (Gen.x d e h4))
      (FreeMonoid.of (Gen.k e f g h h5 h6 h7) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
        FreeMonoid.ofList (negw td e) * FreeMonoid.ofList (F ++ A) *
        FreeMonoid.ofList (negw te d) * FreeMonoid.of (Gen.x d e h4)) := by
    have e1 : FreeMonoid.ofList ((Gen.k e f g h h5 h6 h7 :: (negw td e ++ F)) ++
        (Gen.k a b c d h1 h2 h3 :: (A ++ negw te d))) * FreeMonoid.of (Gen.x d e h4) =
        FreeMonoid.of (Gen.k e f g h h5 h6 h7) * FreeMonoid.ofList (negw td e ++ F) *
          FreeMonoid.of (Gen.k a b c d h1 h2 h3) * FreeMonoid.ofList (A ++ negw te d) *
          FreeMonoid.of (Gen.x d e h4) := by
      simp [FreeMonoid.ofList_append, mul_assoc]
    rw [e1]
    refine (((((Derivable.refl _).mul (kE td)).mul (Derivable.refl _)).mul (Derivable.refl _)).mul
      (Derivable.refl _)).trans ?_
    have e2 : FreeMonoid.of (Gen.k e f g h h5 h6 h7) * (FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
        FreeMonoid.ofList (negw td e ++ F) * FreeMonoid.of (Gen.k a b c d h1 h2 h3)) *
        FreeMonoid.of (Gen.k a b c d h1 h2 h3) * FreeMonoid.ofList (A ++ negw te d) *
        FreeMonoid.of (Gen.x d e h4) =
        FreeMonoid.of (Gen.k e f g h h5 h6 h7) * FreeMonoid.of (Gen.k a b c d h1 h2 h3) *
          FreeMonoid.ofList (negw td e ++ F) *
          (FreeMonoid.of (Gen.k a b c d h1 h2 h3) * FreeMonoid.of (Gen.k a b c d h1 h2 h3)) *
          FreeMonoid.ofList (A ++ negw te d) * FreeMonoid.of (Gen.x d e h4) := by
      simp only [mul_assoc]
    rw [e2]
    refine (((((Derivable.refl _).mul (sq_derivable (Gen.k a b c d h1 h2 h3))).mul
      (Derivable.refl _)).mul (Derivable.refl _))).trans ?_
    exact deq (by simp only [FreeMonoid.ofList_append, mul_assoc, one_mul, mul_one])
  have r23 := ((Derivable.refl (FreeMonoid.of (Gen.k e f g h h5 h6 h7) *
    FreeMonoid.of (Gen.k a b c d h1 h2 h3))).mul (r2.trans (r3.mul (Derivable.refl _))))
  exact r4.trans ((deq (by simp only [mul_assoc])).trans (r23.symm.trans
    ((deq (by simp only [mul_assoc])).trans r1.symm)))

/-! ## Closing the square -/

/-- The square with the path `T⁻¹ X T N_t`, given the levels along `T` after two
syllables at `s` and at `r = X s`. -/
theorem finish1223 {s : O_ZHalf n} (hs : s ≠ 1) (hk : 0 < lde s) {X : Gen n}
    (hle : level (sem n X * s) ≤ level s) (T S : List (Gen n)) (hlen : T.length = 5)
    (hsyllt : syll (next s) = S)
    (hS : ∀ j, 0 < j → ∀ x ∈ S.drop j, SPBelow s x)
    (hTs : ∀ j ≤ 5, level (FreeMonoid.lift (sem n) (FreeMonoid.ofList (T.drop j)) *
      next (next s)) < level s)
    (hTr : ∀ j ≤ 5, level (FreeMonoid.lift (sem n) (FreeMonoid.ofList (T.drop j)) *
      next (next (sem n X * s))) < level s)
    (hder : Derivable (Table1 n) (FreeMonoid.ofList (npath 2 (sem n X * s)) * FreeMonoid.of X)
      (FreeMonoid.ofList (T.reverse ++ [X] ++ T ++ S) * FreeMonoid.ofList (syll s))) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n X * s)) * FreeMonoid.of X)
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  set P := T.reverse ++ [X] ++ T ++ S with hPdef
  have hsem := derivable_sound sound hder
  simp only [map_mul, FreeMonoid.lift_eval_of] at hsem
  have hq : FreeMonoid.lift (sem n) (FreeMonoid.ofList P) * next s =
      next (next (sem n X * s)) := by
    have := iterN_eq 2 (sem n X * s)
    rw [show iterN 2 (sem n X * s) = next (next (sem n X * s)) from rfl] at this
    rw [this, next, ← mul_assoc, ← hsem, mul_assoc]
  refine square hs hle 2 P (Or.inl two_pos) hder ?_
  intro i hi0 hi
  have hlenP : P.length = 11 + S.length := by simp [hPdef, hlen]; omega
  have htF : FixCols (mat (next s)) (pivotJ s) := fixCols_next s
  have htL := level_next_lt s hs
  by_cases h11 : 11 ≤ i
  · obtain ⟨k, rfl⟩ : ∃ k, i = (T.reverse ++ [X] ++ T).length + k := ⟨i - 11, by simp [hlen]; omega⟩
    have e : P.drop ((T.reverse ++ [X] ++ T).length + k) = S.drop k := by
      rw [hPdef, List.drop_length_add_append]
    rw [e]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [List.drop_zero, ← hsyllt]
      have := hTs 5 le_rfl
      rw [List.drop_eq_nil_of_le (by omega : T.length ≤ 5), FreeMonoid.ofList_nil, map_one,
        one_mul] at this
      exact this
    · exact (level_sp_word hs hk (S.drop k) (hS k hk0) htF htL).2
  by_cases h6 : 6 ≤ i
  · obtain ⟨j, rfl⟩ : ∃ j, i = (T.reverse ++ [X]).length + j := ⟨i - 6, by simp [hlen]; omega⟩
    have hj : j ≤ T.length := by simp [hlen] at h11 ⊢; omega
    have e : P.drop ((T.reverse ++ [X]).length + j) = T.drop j ++ S := by
      rw [hPdef, List.append_assoc (T.reverse ++ [X]), List.drop_length_add_append,
        List.drop_append_of_le_length hj]
    rw [e, FreeMonoid.ofList_append, map_mul, mul_assoc, ← hsyllt]
    exact hTs j (by omega)
  · -- the states on the side of `q`: signed permutations of `next (next r)` along `T`
    push Not at h6
    have hiT : i ≤ T.reverse.length := by simp [hlen]; omega
    have hAB : P = P.take i ++ P.drop i := (List.take_append_drop i P).symm
    have htake : P.take i = T.reverse.take i := by
      rw [hPdef, List.append_assoc, List.append_assoc, List.take_append_of_le_length hiT]
    have hB : FreeMonoid.lift (sem n) (FreeMonoid.ofList (P.drop i)) * next s =
        FreeMonoid.lift (sem n) (FreeMonoid.ofList (P.take i).reverse) *
          next (next (sem n X * s)) := by
      have hsplit : FreeMonoid.lift (sem n) (FreeMonoid.ofList P) =
          FreeMonoid.lift (sem n) (FreeMonoid.ofList (P.take i)) *
            FreeMonoid.lift (sem n) (FreeMonoid.ofList (P.drop i)) := by
        conv_lhs => rw [← List.take_append_drop i P]
        rw [FreeMonoid.ofList_append, map_mul]
      rw [← hq, hsplit, mul_assoc, ← mul_assoc, lift_rev_mul, one_mul]
    rw [hB, htake, List.take_reverse, List.reverse_reverse, hlen]
    exact hTr (5 - i) (by omega)

theorem signs_append (U : O_ZHalf n) (l₁ l₂ : List (Fin n)) :
    signs U (l₁ ++ l₂) = signs U l₁ ++ signs U l₂ := by
  simp [signs, List.filter_append]

theorem signs_one (U : O_ZHalf n) (x : Fin n) : signs U [x] = negw (tau (wint U x)) x := by
  rw [signs_cons]; simp [signs, negw]

/-- Subcase 1.2.2.3 with `u_e` odd. -/
theorem squareX_odd' {s : O_ZHalf n} (hs : s ≠ 1) {x y : Fin n} (hxy : x < y)
    (hy : y.val = x.val + 1) (hle : level (sem n (Gen.x x y hxy) * s) ≤ level s)
    (hk : 0 < lde s) {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r)
    (h2 : d = x ∧ y ∈ oddS s) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.x x y hxy) * s)) *
        FreeMonoid.of (Gen.x x y hxy)) (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  obtain ⟨hdx, he⟩ := h2
  subst hdx
  have hU := pivot_pos hs
  have v1 := Fin.lt_def.1 hab; have v2 := Fin.lt_def.1 hbc; have v3 := Fin.lt_def.1 hcd
  have v4 := Fin.lt_def.1 hxy
  -- the next three odd entries `f, g, h`
  have hcard : 8 ≤ (oddS s).card := by
    have h4 : 4 ∣ (oddS s).card := four_dvd_card_oddSet (pcol_norm s hU) hk (intAt_lde s)
    have hsub : ({a, b, c, d, y} : Finset (Fin n)) ⊆ oddS s := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
    have h5 : ({a, b, c, d, y} : Finset (Fin n)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
        Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
        Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
        Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega), Finset.card_singleton]
    have := Finset.card_le_card hsub
    rw [h5] at this
    omega
  set E := (oddS s).orderEmbOfFin rfl with hEdef
  have hE4 : E ⟨4, by omega⟩ = y := by
    apply orderEmbOfFin_eq_of_count rfl _ he
    have : (oddS s).filter (· < y) = {a, b, c, d} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hzy⟩
        have := Fin.lt_def.1 hzy
        rcases hrest z hz with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · have := Fin.lt_def.1 h; omega
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨ha, Fin.lt_def.2 (by omega)⟩
        · exact ⟨hb, Fin.lt_def.2 (by omega)⟩
        · exact ⟨hc, Fin.lt_def.2 (by omega)⟩
        · exact ⟨hd, hxy⟩
    rw [this, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega), Finset.card_singleton]
  set f := E ⟨5, by omega⟩
  set g := E ⟨6, by omega⟩
  set h := E ⟨7, by omega⟩
  have hyf : y < f := by rw [← hE4]; exact E.strictMono (Fin.mk_lt_mk.2 (by omega))
  have hfg : f < g := E.strictMono (Fin.mk_lt_mk.2 (by omega))
  have hgh : g < h := E.strictMono (Fin.mk_lt_mk.2 (by omega))
  have hf : f ∈ oddS s := Finset.orderEmbOfFin_mem _ rfl _
  have hg : g ∈ oddS s := Finset.orderEmbOfFin_mem _ rfl _
  have hh : h ∈ oddS s := Finset.orderEmbOfFin_mem _ rfl _
  have hrest8 : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = y ∨ r = f ∨ r = g ∨ r = h ∨
      h < r := by
    intro r hr
    rcases hrest r hr with e | e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    right; right; right; right
    have := Fin.lt_def.1 e
    by_cases ry : r = y
    · exact Or.inl ry
    right
    have hyr : y < r := Fin.lt_def.2 (by have := Fin.val_injective.ne ry; omega)
    have : r ∈ Set.range E := by rw [hEdef, Finset.range_orderEmbOfFin]; exact hr
    obtain ⟨i, rfl⟩ := this
    have hi4 : 4 < i.val := by
      rw [← hE4] at hyr
      exact Fin.lt_def.1 (E.lt_iff_lt.1 hyr)
    by_cases i5 : i.val = 5
    · left; exact congrArg E (Fin.ext i5)
    by_cases i6 : i.val = 6
    · right; left; exact congrArg E (Fin.ext i6)
    by_cases i7 : i.val = 7
    · right; right; left; exact congrArg E (Fin.ext i7)
    right; right; right
    exact E.strictMono (Fin.mk_lt_mk.2 (by omega))
  -- the state `r = X_[d,y] s`
  have hcV : IsCol (gact (Gen.x d y hxy) (pcol s)) (lde s)
      (fun z => wint s (Equiv.swap d y z)) := isCol_x (isCol_pcol s) hxy
  obtain ⟨hpV, hcolV, hkV⟩ := state_gen hs (extent_lt_of_le hs hle) hcV hk (r := a)
    (by rw [Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_lt (by exact Fin.lt_def.2 (by omega)))
      (Fin.ne_of_lt (by exact Fin.lt_def.2 (by omega)))]; exact (mem_oddS_iff a).1 ha)
  set r := sem n (Gen.x d y hxy) * s
  have hr1 : r ≠ 1 := fun e => by
    have := hpV; rw [e, (pivotJ_eq_zero_iff 1).2 rfl] at this; omega
  have hkr : 0 < lde r := by rw [hkV]; exact hk
  have hcr : IsCol (pcol r) (lde r) (fun z => wint s (Equiv.swap d y z)) := by
    rw [hcolV, hkV]; exact hcV
  have hwr : ∀ z, wint r z = wint s (Equiv.swap d y z) := fun z => wint_eq hcr z
  have hwr' : ∀ z, z ≠ d → z ≠ y → wint r z = wint s z := fun z h1 h2 => by
    rw [hwr, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hor : oddS r = oddS s := by
    ext z
    rw [mem_oddS_iff, mem_oddS_iff, hwr]
    by_cases zd : z = d
    · subst zd; rw [Equiv.swap_apply_left]
      exact ⟨fun _ => (mem_oddS_iff _).1 hd, fun _ => (mem_oddS_iff _).1 he⟩
    by_cases zy : z = y
    · subst zy; rw [Equiv.swap_apply_right]
      exact ⟨fun _ => (mem_oddS_iff _).1 he, fun _ => (mem_oddS_iff _).1 hd⟩
    rw [Equiv.swap_apply_of_ne_of_ne zd zy]
  have ne : ∀ {u v : Fin n}, u.val < v.val → u ≠ v := fun huv e => by subst e; omega
  have ne' : ∀ {u v : Fin n}, u.val < v.val → v ≠ u := fun huv e => by subst e; omega
  have vf := Fin.lt_def.1 hyf; have vg := Fin.lt_def.1 hfg; have vh := Fin.lt_def.1 hgh
  -- the sums of the eight entries agree at `s` and `r`
  have hFs : ∀ z ∈ oddS s, fix4 (wint s z) % 4 = 1 := fun z hz => fix4_mod ((mem_oddS_iff z).1 hz)
  have hsum_r : fix4 (wint r a) + fix4 (wint r b) + fix4 (wint r c) + fix4 (wint r d) +
      fix4 (wint r y) + fix4 (wint r f) + fix4 (wint r g) + fix4 (wint r h) =
      fix4 (wint s a) + fix4 (wint s b) + fix4 (wint s c) + fix4 (wint s d) +
      fix4 (wint s y) + fix4 (wint s f) + fix4 (wint s g) + fix4 (wint s h) := by
    rw [hwr' a (ne (by omega)) (ne (by omega)), hwr' b (ne (by omega)) (ne (by omega)),
      hwr' c (ne (by omega)) (ne (by omega)), hwr d, Equiv.swap_apply_left, hwr y,
      Equiv.swap_apply_right, hwr' f (ne' (by omega)) (ne' (by omega)),
      hwr' g (ne' (by omega)) (ne' (by omega)), hwr' h (ne' (by omega)) (ne' (by omega))]
    ring
  have hJ : h.val < pivotJ s := le_pidx_of_odd hs hh
  -- the syllables
  obtain ⟨hs1, hs2, -, -⟩ := eight_syll hs hk hab hbc hcd hxy hyf hfg hgh ha hb hc hd he hf hg hh
    hrest8
  obtain ⟨hr1s, hr2s, -, -⟩ := eight_syll hr1 hkr hab hbc hcd hxy hyf hfg hgh (hor ▸ ha)
    (hor ▸ hb) (hor ▸ hc) (hor ▸ hd) (hor ▸ he) (hor ▸ hf) (hor ▸ hg) (hor ▸ hh) (hor ▸ hrest8)
  set A := signs s [a, b, c]
  set F := signs s [f, g, h]
  have hsA : signs s [a, b, c, d] = A ++ negw (tau (wint s d)) d := by
    rw [show [a, b, c, d] = [a, b, c] ++ [d] from rfl, signs_append, signs_one]
  have hsF : signs s [y, f, g, h] = negw (tau (wint s y)) y ++ F := by
    rw [signs_cons]; rfl
  have hrA : signs r [a, b, c, d] = A ++ negw (tau (wint s y)) d := by
    rw [show [a, b, c, d] = [a, b, c] ++ [d] from rfl, signs_append,
      signs_congr s r [a, b, c] (fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> exact hwr' _ (ne (by omega)) (ne (by omega))),
      signs_one, hwr d, Equiv.swap_apply_left]
  have hrF : signs r [y, f, g, h] = negw (tau (wint s d)) y ++ F := by
    rw [signs_cons, hwr y, Equiv.swap_apply_right, signs_congr s r [f, g, h] (fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> exact hwr' _ (ne' (by omega)) (ne' (by omega)))]
    rfl
  have hA : ∀ z ∈ A, ∃ q, z = Gen.neg q ∧ q.val < d.val := fun z hz => by
    obtain ⟨q, hq, rfl⟩ := mem_signs hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ⟨q, rfl, by rcases hq with rfl | rfl | rfl <;> omega⟩
  have hF : ∀ z ∈ F, ∃ q, z = Gen.neg q ∧ y.val < q.val := fun z hz => by
    obtain ⟨q, hq, rfl⟩ := mem_signs hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ⟨q, rfl, by rcases hq with rfl | rfl | rfl <;> omega⟩
  have hS : ∀ j, 0 < j → ∀ z ∈ (syll (next s)).drop j, SPBelow s z := by
    intro j hj z hz
    rw [hs2] at hz
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hz' := List.mem_of_mem_drop (by simpa using hz)
    obtain ⟨q, hq, rfl⟩ := mem_signs hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ⟨by simp [Gen.tag], by simp only [extent]; rcases hq with rfl | rfl | rfl | rfl <;> omega⟩
  have hnp : npath 2 r = syll (next r) ++ syll r := by
    show npath 1 (next r) ++ syll r = _
    rw [npath_one]
  have hs4 : (fix4 (wint s a) + fix4 (wint s b) + fix4 (wint s c) + fix4 (wint s d) +
      fix4 (wint s y) + fix4 (wint s f) + fix4 (wint s g) + fix4 (wint s h)) % 8 = 4 ∨
      (fix4 (wint s a) + fix4 (wint s b) + fix4 (wint s c) + fix4 (wint s d) +
      fix4 (wint s y) + fix4 (wint s f) + fix4 (wint s g) + fix4 (wint s h)) % 8 = 0 := by
    have := hFs a ha; have := hFs b hb; have := hFs c hc; have := hFs d hd
    have := hFs y he; have := hFs f hf; have := hFs g hg; have := hFs h hh
    omega
  rcases hs4 with h4 | h0
  · -- `ū ᵀ ū ≡ 0 (mod 16)`: `W = (−1)_[a] (−1)_[e] X_[a,e]`, relation (6a)
    refine finish1223 hs hk hle [Gen.k y f g h hyf hfg hgh, Gen.k a b c d hab hbc hcd, Gen.neg a,
      Gen.neg y, Gen.x a y (hab.trans (hbc.trans (hcd.trans hxy)))] _ rfl rfl hS
      (eight_lev_e hs hk hab hbc hcd hxy hyf hfg hgh ha hb hc hd he hf hg hh hrest8 h4)
      (fun j hj => lt_of_lt_of_le (eight_lev_e hr1 hkr hab hbc hcd hxy hyf hfg hgh (hor ▸ ha)
        (hor ▸ hb) (hor ▸ hc) (hor ▸ hd) (hor ▸ he) (hor ▸ hf) (hor ▸ hg) (hor ▸ hh)
        (hor ▸ hrest8) (by rw [hsum_r]; exact h4) j hj) hle) ?_
    rw [hnp, hr1s, hr2s, hrA, hrF, hs2, hsF, hs1, hsA]
    exact der1223 hab hbc hcd hxy hyf hfg hgh _ (rel1223_e hab hbc hcd hxy hyf hfg hgh) A F hA hF
      _ _
  · -- `ū ᵀ ū ≡ 8 (mod 16)`: `W = (−1)_[a] (−1)_[h] X_[a,h]`, Proposition A.16
    refine finish1223 hs hk hle [Gen.k y f g h hyf hfg hgh, Gen.k a b c d hab hbc hcd, Gen.neg a,
      Gen.neg h, Gen.x a h (hab.trans (hbc.trans (hcd.trans (hxy.trans (hyf.trans
      (hfg.trans hgh))))))] _ rfl rfl hS
      (eight_lev_h hs hk hab hbc hcd hxy hyf hfg hgh ha hb hc hd he hf hg hh hrest8 h0)
      (fun j hj => lt_of_lt_of_le (eight_lev_h hr1 hkr hab hbc hcd hxy hyf hfg hgh (hor ▸ ha)
        (hor ▸ hb) (hor ▸ hc) (hor ▸ hd) (hor ▸ he) (hor ▸ hf) (hor ▸ hg) (hor ▸ hh)
        (hor ▸ hrest8) (by rw [hsum_r]; exact h0) j hj) hle) ?_
    rw [hnp, hr1s, hr2s, hrA, hrF, hs2, hsF, hs1, hsA]
    exact der1223 hab hbc hcd hxy hyf hfg hgh _ (rel1223_h hab hbc hcd hxy hyf hfg hgh) A F hA hF
      _ _

end QCert.LiRossSelinger
