/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Case 3.2: `G = K_[0,1,2,3]` at `k > 0`

Subcase 3.2.1, `{a,b,c,d} ∩ {0,1,2,3} = ∅` (`squareK_disj`): the entries
`0, …, 3` of `u = 2^k v` are even, so `K` keeps the scale and makes them all
odd or all even (the four sums differ by even numbers).  All odd raises the
level by four odd entries (excluded by the hypothesis); all even keeps the
syllable, and `K` closes the square by (2e) and (2f).
-/
import QCert.LiRossSelinger.CasePair

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

theorem nd8 {a₀ a₁ a₂ a₃ a b c d : Fin n} (h₁ : a₀ < a₁) (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (h₄ : a₃ < a) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    [a, b, c, d, a₀, a₁, a₂, a₃].Nodup := by
  have := Fin.lt_def.1 h₁; have := Fin.lt_def.1 h₂; have := Fin.lt_def.1 h₃
  have := Fin.lt_def.1 h₄; have := Fin.lt_def.1 hab; have := Fin.lt_def.1 hbc
  have := Fin.lt_def.1 hcd
  apply nodup_vals
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
  omega

/-- Subcase 3.2.1: no first odd entry among the indices of `K`. -/
theorem squareK_disj {s : O_ZHalf n} (hs : s ≠ 1) {a₀ a₁ a₂ a₃ : Fin n} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) (h3a : a₃ < a) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  set K := Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃
  have v1 := Fin.lt_def.1 h₁; have v2 := Fin.lt_def.1 h₂; have v3 := Fin.lt_def.1 h₃
  have v4 := Fin.lt_def.1 h3a; have va := Fin.lt_def.1 hab; have vb := Fin.lt_def.1 hbc
  have vc := Fin.lt_def.1 hcd
  -- the entries `a₀, …, a₃` are even
  have hge : ∀ r ∈ oddS s, a.val ≤ r.val := by
    intro r hr
    rcases hrest r hr with e | e | e | e | e <;> (try rw [e]) <;>
      (try have := Fin.lt_def.1 e) <;> omega
  have hev : ∀ r : Fin n, r.val ≤ a₃.val → wint s r % 2 = 0 := by
    intro r hr
    by_contra h
    have : r ∈ oddS s := (mem_oddS_iff r).2 (Int.odd_iff.2 (by omega))
    have := hge r this; omega
  have e0 := hev a₀ (by omega); have e1 := hev a₁ (by omega)
  have e2 := hev a₂ (by omega); have e3 := hev a₃ le_rfl
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  have hcV := isCol_k (isCol_pcol s) h₁ h₂ h₃ hsum
  set u' : Fin n → ℤ := fun r =>
      if r = a₀ then (wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃) / 2
      else if r = a₁ then (wint s a₀ - wint s a₁ + wint s a₂ - wint s a₃) / 2
      else if r = a₂ then (wint s a₀ + wint s a₁ - wint s a₂ - wint s a₃) / 2
      else if r = a₃ then (wint s a₀ - wint s a₁ - wint s a₂ + wint s a₃) / 2
      else wint s r with hu'
  have d01 : a₀ ≠ a₁ := ne_of_lt h₁
  have d02 : a₀ ≠ a₂ := ne_of_lt (h₁.trans h₂)
  have d03 : a₀ ≠ a₃ := ne_of_lt (h₁.trans (h₂.trans h₃))
  have d12 : a₁ ≠ a₂ := ne_of_lt h₂
  have d13 : a₁ ≠ a₃ := ne_of_lt (h₂.trans h₃)
  have d23 : a₂ ≠ a₃ := ne_of_lt h₃
  have hout : ∀ r : Fin n, r ∉ [a₀, a₁, a₂, a₃] → u' r = wint s r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hu', hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  -- the four new entries have the parity of the first
  have hpar : ∀ r ∈ [a₀, a₁, a₂, a₃],
      (u' r % 2 = 1 ↔ (wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃) / 2 % 2 = 1) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp [hu', d01, d02, d03, d12, d13, d23, d01.symm, d02.symm, d03.symm, d12.symm,
        d13.symm, d23.symm] <;> omega
  have hnotK : ∀ r ∈ oddS s, r ∉ [a₀, a₁, a₂, a₃] := by
    intro r hr hK
    have := hge r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
    rcases hK with rfl | rfl | rfl | rfl <;> omega
  have hoa : Odd (u' a) := by
    rw [hout a (hnotK a ha)]; exact (mem_oddS_iff a).1 ha
  obtain ⟨hpV, hcolV, hkV⟩ := state_gen hs (extent_lt_of_le hs hle) hcV hk hoa
  set V := sem n K * s
  have hcV' : IsCol (pcol V) (lde V) u' := by rw [hcolV, hkV]; exact hcV
  by_cases hodd : (wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃) / 2 % 2 = 1
  · -- the level goes up by four odd entries
    exfalso
    apply absurd hle
    apply not_le.2
    have hsub : (Finset.univ.filter fun r => Odd (wint s r)) ⊂
        (Finset.univ.filter fun r => Odd (u' r)) := by
      refine ⟨fun r hr => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        rw [hout r (hnotK r ((mem_oddS_iff r).2 hr))]; exact hr
      · have h0 : a₀ ∈ Finset.univ.filter fun r => Odd (u' r) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Int.odd_iff.2 ((hpar a₀ (by simp)).2 hodd)
        have := hsub h0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        have := Int.odd_iff.1 this
        omega
    have hcard := Finset.card_lt_card hsub
    rw [← nodd_eq hcV' (by rw [hkV]; exact hk)] at hcard
    rw [show (Finset.univ.filter fun r => Odd (wint s r)) = oddS s from (oddS_eq (isCol_pcol s)).symm]
      at hcard
    rw [level_eq_mk s hU, level_eq_mk V (by rw [hpV]; exact hU), hpV, hkV, mkLevel_lt_iff]
    right; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    unfold nodd; rw [if_neg (by omega)]; exact hcard
  -- the entries stay even: same odd entries, same syllable
  have hsame : ∀ r, Odd (u' r) ↔ Odd (wint s r) := by
    intro r
    by_cases hr : r ∈ [a₀, a₁, a₂, a₃]
    · have h1 : ¬ Odd (u' r) := fun h => hodd ((hpar r hr).1 (Int.odd_iff.1 h))
      have h2 : ¬ Odd (wint s r) := fun h => hnotK r ((mem_oddS_iff r).2 h) hr
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    · rw [hout r hr]
  have hoV : oddS V = oddS s := by
    rw [oddS_eq hcV', oddS_eq (isCol_pcol s)]
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hsame r
  have hsylls : syll s = Gen.k a b c d hab hbc hcd :: signs s [a, b, c, d] :=
    syll_eq_pos s hU hk hab hbc hcd ha hb hc hd hrest
  have hsyllV : syll V = syll s := by
    rw [hsylls, syll_eq_pos V (by rw [hpV]; exact hU) (by rw [hkV]; exact hk) hab hbc hcd
      (hoV ▸ ha) (hoV ▸ hb) (hoV ▸ hc) (hoV ▸ hd) (hoV ▸ hrest)]
    congr 1
    apply signs_congr
    intro r hr
    rw [wint_eq hcV' r, hout r (hnotK r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [ha, hb, hc, hd]))]
  refine square_short hs hle [K] (by simp) ?_
  rw [FreeMonoid.ofList_singleton, hsyllV]
  apply comm_list
  intro g hg
  rw [hsylls] at hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact Derivable.of (Table1.r2f a b c d a₀ a₁ a₂ a₃ hab hbc hcd h₁ h₂ h₃
      (nd8 h₁ h₂ h₃ h3a hab hbc hcd))
  · obtain ⟨r, hr, rfl⟩ := mem_signs hg
    have hra : a.val ≤ r.val := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> omega
    exact Derivable.of (Table1.r2e r a₀ a₁ a₂ a₃ h₁ h₂ h₃
      (nd5 h₁ h₂ h₃ (Fin.lt_def.2 (by omega))))

end QCert.LiRossSelinger
