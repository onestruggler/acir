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

end QCert.LiRossSelinger
