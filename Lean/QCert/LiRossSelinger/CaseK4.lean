/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcase 3.2.5: `K_[0,1,2,3]` on the first four odd entries

The first four odd entries are `0, 1, 2, 3`.  `K` makes them all even when
evenly many of them are `≡ 3 (mod 4)` (Lemma A.2), and then `G s` lies below
`s` and `K ≈ V · K S` closes the square; otherwise they stay odd, the
syllable of `G s` is `K S'`, and `K S' K ≈ V · K S` closes it.  `V` is a
word of `(−1)` and `X` letters (Corollaries A.13, A.14), found by a search
and checked by the kernel (`Rel325`), so the path stays below the level
(`square_sp0`).
-/
import QCert.LiRossSelinger.PathSP
import QCert.LiRossSelinger.Rel325

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-- `K` on four odd integers: the four new entries all have the parity of the
number of entries `≡ 3 (mod 4)` (Lemma A.2). -/
theorem k4_par (w0 w1 w2 w3 : ℤ) (o0 : w0 % 2 = 1) (o1 : w1 % 2 = 1) (o2 : w2 % 2 = 1)
    (o3 : w3 % 2 = 1) :
    (w0 + w1 + w2 + w3) / 2 % 2 = (if xor (xor (xor (tau w0) (tau w1)) (tau w2)) (tau w3) then 1 else 0) ∧
    (w0 - w1 + w2 - w3) / 2 % 2 = (if xor (xor (xor (tau w0) (tau w1)) (tau w2)) (tau w3) then 1 else 0) ∧
    (w0 + w1 - w2 - w3) / 2 % 2 = (if xor (xor (xor (tau w0) (tau w1)) (tau w2)) (tau w3) then 1 else 0) ∧
    (w0 - w1 - w2 + w3) / 2 % 2 = (if xor (xor (xor (tau w0) (tau w1)) (tau w2)) (tau w3) then 1 else 0) := by
  unfold tau
  by_cases h0 : w0 % 4 = 3 <;> by_cases h1 : w1 % 4 = 3 <;> by_cases h2 : w2 % 4 = 3 <;>
    by_cases h3 : w3 % 4 = 3 <;> simp [h0, h1, h2, h3] <;> omega

theorem k4_back (w0 w1 w2 w3 : ℤ) (o0 : w0 % 2 = 1) (o1 : w1 % 2 = 1) (o2 : w2 % 2 = 1)
    (o3 : w3 % 2 = 1) :
    ((w0 + w1 + w2 + w3) / 2 + (w0 - w1 + w2 - w3) / 2 + (w0 + w1 - w2 - w3) / 2 +
      (w0 - w1 - w2 + w3) / 2) / 2 = w0 := by
  omega

theorem sp_rename4 {s : O_ZHalf n} {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁) (h₂ : a₁ < a₂)
    (h₃ : a₂ < a₃) (hJ : a₃.val < pivotJ s) (V : List (Gen 4)) (hV : ∀ g ∈ V, g.tag ≠ 2) :
    ∀ x ∈ V.map (Gen.rename (emb4 h₁ h₂ h₃)), SPBelow s x := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
  refine ⟨by rw [tag_rename]; exact hV g hg, ?_⟩
  have := extent_rename_le (emb4 h₁ h₂ h₃) g 3 (extent_le_last g)
  rw [emb4_3] at this
  omega

theorem sgn4_rename {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁) (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (t0 t1 t2 t3 : Bool) :
    (sgn4 t0 t1 t2 t3).map (Gen.rename (emb4 h₁ h₂ h₃)) =
      negw t0 a₀ ++ negw t1 a₁ ++ negw t2 a₂ ++ negw t3 a₃ := by
  simp only [sgn4, List.map_append, negw_rename, emb4_0, emb4_1, emb4_2, emb4_3]

/-- Subcase 3.2.5. -/
theorem squareK_four {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (ha : a₀ ∈ oddS s) (hb : a₁ ∈ oddS s) (hc : a₂ ∈ oddS s) (hd : a₃ ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a₀ ∨ r = a₁ ∨ r = a₂ ∨ r = a₃ ∨ a₃ < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  set Kg := Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃ with hKg
  have hJ : a₃.val < pivotJ s := extent_lt_of_le hs hle
  have o0 := Int.odd_iff.1 ((mem_oddS_iff a₀).1 ha)
  have o1 := Int.odd_iff.1 ((mem_oddS_iff a₁).1 hb)
  have o2 := Int.odd_iff.1 ((mem_oddS_iff a₂).1 hc)
  have o3 := Int.odd_iff.1 ((mem_oddS_iff a₃).1 hd)
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  have hcV := isCol_k (isCol_pcol s) h₁ h₂ h₃ hsum
  obtain ⟨u', hu'⟩ : ∃ u' : Fin n → ℤ, u' = fun r =>
      if r = a₀ then (wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃) / 2
      else if r = a₁ then (wint s a₀ - wint s a₁ + wint s a₂ - wint s a₃) / 2
      else if r = a₂ then (wint s a₀ + wint s a₁ - wint s a₂ - wint s a₃) / 2
      else if r = a₃ then (wint s a₀ - wint s a₁ - wint s a₂ + wint s a₃) / 2
      else wint s r := ⟨_, rfl⟩
  rw [← hu'] at hcV
  have d01 : a₀ ≠ a₁ := ne_of_lt h₁
  have d02 : a₀ ≠ a₂ := ne_of_lt (h₁.trans h₂)
  have d03 : a₀ ≠ a₃ := ne_of_lt (h₁.trans (h₂.trans h₃))
  have d12 : a₁ ≠ a₂ := ne_of_lt h₂
  have d13 : a₁ ≠ a₃ := ne_of_lt (h₂.trans h₃)
  have d23 : a₂ ≠ a₃ := ne_of_lt h₃
  have hv0 : u' a₀ = (wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃) / 2 := by simp [hu']
  have hv1 : u' a₁ = (wint s a₀ - wint s a₁ + wint s a₂ - wint s a₃) / 2 := by
    simp [hu', d01.symm]
  have hv2 : u' a₂ = (wint s a₀ + wint s a₁ - wint s a₂ - wint s a₃) / 2 := by
    simp [hu', d02.symm, d12.symm]
  have hv3 : u' a₃ = (wint s a₀ - wint s a₁ - wint s a₂ + wint s a₃) / 2 := by
    simp [hu', d03.symm, d13.symm, d23.symm]
  have hout : ∀ r, r ≠ a₀ → r ≠ a₁ → r ≠ a₂ → r ≠ a₃ → u' r = wint s r := by
    intro r e0 e1 e2 e3; simp [hu', e0, e1, e2, e3]
  obtain ⟨p0, p1, p2, p3⟩ := k4_par _ _ _ _ o0 o1 o2 o3
  rw [← hv0] at p0; rw [← hv1] at p1; rw [← hv2] at p2; rw [← hv3] at p3
  have hsylls := syll_eq_pos s hU hk h₁ h₂ h₃ ha hb hc hd hrest
  have hSs : signs s [a₀, a₁, a₂, a₃] = (sgn4 (tau (wint s a₀)) (tau (wint s a₁))
      (tau (wint s a₂)) (tau (wint s a₃))).map (Gen.rename (emb4 h₁ h₂ h₃)) := by
    rw [signs4, sgn4_rename]
  have hKr : Gen.rename (emb4 h₁ h₂ h₃) K4 = Kg := rfl
  by_cases hpar : xor (xor (xor (tau (wint s a₀)) (tau (wint s a₁))) (tau (wint s a₂)))
      (tau (wint s a₃)) = false
  · -- all four new entries even: `G s` lies below `s`
    rw [hpar] at p0 p1 p2 p3
    simp only [Bool.false_eq_true, ↓reduceIte] at p0 p1 p2 p3
    have hlt : level (sem n Kg * s) < level s := by
      have hl : BelowJ (pivotJ s) [Kg] := by
        intro g hg; rw [List.mem_singleton] at hg; rw [hg]; exact hJ
      have := level_lt_of_col hs hk [Kg] hl (u' := u') (by rw [wact_single]; exact hcV)
        (fun r hr => by
          by_cases e0 : r = a₀
          · subst e0; exact absurd (Int.odd_iff.1 hr) (by omega)
          by_cases e1 : r = a₁
          · subst e1; exact absurd (Int.odd_iff.1 hr) (by omega)
          by_cases e2 : r = a₂
          · subst e2; exact absurd (Int.odd_iff.1 hr) (by omega)
          by_cases e3 : r = a₃
          · subst e3; exact absurd (Int.odd_iff.1 hr) (by omega)
          rwa [hout r e0 e1 e2 e3] at hr)
        (r₀ := a₀) (Int.odd_iff.2 o0) (fun h => by have := Int.odd_iff.1 h; omega)
      simpa [lift_single] using this
    refine square_sp0 hs hk hle 0 (Or.inr hlt) _ (sp_rename4 h₁ h₂ h₃ hJ
      (V325e (tau (wint s a₀)) (tau (wint s a₁)) (tau (wint s a₂)) (tau (wint s a₃)))
      (tag325e _ _ _ _)) ?_
    have hh := derivable_rename (emb4 h₁ h₂ h₃) (checkD_sound (chk325e _ _ _ _ hpar))
    rw [renW_ofList, renW_ofList] at hh
    rw [hsylls, hSs, show FreeMonoid.ofList (npath 0 (sem n Kg * s)) * FreeMonoid.of Kg =
      FreeMonoid.ofList [Kg] by simp [npath], ← FreeMonoid.ofList_append]
    convert hh using 2
    simp only [List.map_append, List.map_cons, hKr]
    try rfl
  · -- all four stay odd: the syllable of `G s` is on the same entries
    have hpar' : xor (xor (xor (tau (wint s a₀)) (tau (wint s a₁))) (tau (wint s a₂)))
        (tau (wint s a₃)) = true := by simpa using hpar
    rw [hpar'] at p0 p1 p2 p3
    simp only [↓reduceIte] at p0 p1 p2 p3
    obtain ⟨hpV, hcolV, hkV⟩ := state_gen hs (g := Kg) hJ hcV hk (r := a₀) (Int.odd_iff.2 p0)
    set V := sem n Kg * s
    have hcV' : IsCol (pcol V) (lde V) u' := by rw [hcolV, hkV]; exact hcV
    have hwV : ∀ r, wint V r = u' r := fun r => wint_eq hcV' r
    have hsame : ∀ r, Odd (u' r) ↔ Odd (wint s r) := by
      intro r
      by_cases e0 : r = a₀
      · subst e0; exact ⟨fun _ => Int.odd_iff.2 o0, fun _ => Int.odd_iff.2 p0⟩
      by_cases e1 : r = a₁
      · subst e1; exact ⟨fun _ => Int.odd_iff.2 o1, fun _ => Int.odd_iff.2 p1⟩
      by_cases e2 : r = a₂
      · subst e2; exact ⟨fun _ => Int.odd_iff.2 o2, fun _ => Int.odd_iff.2 p2⟩
      by_cases e3 : r = a₃
      · subst e3; exact ⟨fun _ => Int.odd_iff.2 o3, fun _ => Int.odd_iff.2 p3⟩
      rw [hout r e0 e1 e2 e3]
    have hoV : oddS V = oddS s := by
      rw [oddS_eq hcV', oddS_eq (isCol_pcol s)]
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hsame r
    have hsyllV : syll V = Kg :: signs V [a₀, a₁, a₂, a₃] :=
      syll_eq_pos V (by rw [hpV]; exact hU) (by rw [hkV]; exact hk) h₁ h₂ h₃ (hoV ▸ ha)
        (hoV ▸ hb) (hoV ▸ hc) (hoV ▸ hd) (hoV ▸ hrest)
    -- the signs at `G s` are oddly many too (`K` is an involution)
    obtain ⟨q0, -, -, -⟩ := k4_par _ _ _ _ p0 p1 p2 p3
    have hback : (u' a₀ + u' a₁ + u' a₂ + u' a₃) / 2 = wint s a₀ := by
      rw [hv0, hv1, hv2, hv3]; exact k4_back _ _ _ _ o0 o1 o2 o3
    have hpar2 : xor (xor (xor (tau (u' a₀)) (tau (u' a₁))) (tau (u' a₂))) (tau (u' a₃)) =
        true := by
      by_contra hne
      rw [Bool.not_eq_true] at hne
      rw [hne, hback] at q0
      simp only [Bool.false_eq_true, ↓reduceIte] at q0
      omega
    have hSV : signs V [a₀, a₁, a₂, a₃] = (sgn4 (tau (u' a₀)) (tau (u' a₁))
        (tau (u' a₂)) (tau (u' a₃))).map (Gen.rename (emb4 h₁ h₂ h₃)) := by
      simp only [signs4, sgn4_rename, hwV]
    refine square_sp0 hs hk hle 1 (Or.inl one_pos) _ (sp_rename4 h₁ h₂ h₃ hJ
      (V325o (tau (wint s a₀)) (tau (wint s a₁)) (tau (wint s a₂)) (tau (wint s a₃))
        (tau (u' a₀)) (tau (u' a₁)) (tau (u' a₂)) (tau (u' a₃)))
      (tag325o _ _ _ _ _ _ _ _)) ?_
    have hh := derivable_rename (emb4 h₁ h₂ h₃) (checkD_sound (chk325o _ _ _ _ _ _ _ _ hpar'
      hpar2))
    rw [renW_ofList, renW_ofList] at hh
    rw [npath_one, hsyllV, hSV, hsylls, hSs, ← FreeMonoid.ofList_singleton,
      ← FreeMonoid.ofList_append, ← FreeMonoid.ofList_append]
    convert hh using 2
    · simp only [List.map_append, List.map_cons, List.map_nil, hKr, List.cons_append]
      try rfl
    · simp only [List.map_append, List.map_cons, hKr]
      try rfl

end QCert.LiRossSelinger
