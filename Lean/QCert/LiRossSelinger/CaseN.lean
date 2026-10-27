/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, the edges `(−1)_[z]` at `k > 0`

Case 2.2 of the proof of Lemma A.20, for any index `z` (the basic edge is
`z = 0`).  If `z` is not one of the first four odd entries, the syllable of
`G s` is that of `s` and the square is closed by `G` (`squareN_out`,
Subcase 2.2.2); if `z` is one of them, `G` only flips the sign that the
syllable puts on `z`, and the two syllables reach the same state
(`squareN_in`, Subcase 2.2.1).
-/
import QCert.LiRossSelinger.CaseX

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

theorem signs_cons (U : O_ZHalf n) (r : Fin n) (l : List (Fin n)) :
    signs U (r :: l) = (if tau (wint U r) then [Gen.neg r] else []) ++ signs U l := by
  unfold signs
  rw [List.filter_cons]
  split_ifs <;> simp

theorem signs_congr (U V : O_ZHalf n) (l : List (Fin n)) (h : ∀ r ∈ l, wint V r = wint U r) :
    signs V l = signs U l := by
  unfold signs
  congr 1
  exact List.filter_congr (fun r hr => by rw [h r hr])

theorem mem_signs {U : O_ZHalf n} {l : List (Fin n)} {g : Gen n} (h : g ∈ signs U l) :
    ∃ r ∈ l, g = Gen.neg r := by
  unfold signs at h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
  exact ⟨r, (List.mem_filter.1 hr).1, rfl⟩

theorem tau_neg {w : ℤ} (hw : Odd w) : tau (-w) = !tau w := by
  obtain ⟨t, rfl⟩ := hw
  unfold tau
  by_cases h : (2 * t + 1) % 4 = 3
  · rw [decide_eq_true h]; simp; omega
  · rw [decide_eq_false h]; simp; omega

/-- A sign letter commutes with a sign letter. -/
theorem neg_comm (r z : Fin n) :
    Derivable (Table1 n) (FreeMonoid.of (Gen.neg r) * FreeMonoid.of (Gen.neg z))
      (FreeMonoid.of (Gen.neg z) * FreeMonoid.of (Gen.neg r)) := by
  by_cases h : r = z
  · subst h; exact Derivable.refl _
  · exact Derivable.of (Table1.r2d r z h)

/-- The state `(−1)_[z] s` at `k > 0`. -/
theorem stateN {s : O_ZHalf n} (hs : s ≠ 1) {z : Fin n}
    (hle : level (sem n (Gen.neg z) * s) ≤ level s) (hk : 0 < lde s) {a : Fin n}
    (ha : a ∈ oddS s) :
    pivotJ (sem n (Gen.neg z) * s) = pivotJ s ∧
      IsCol (pcol (sem n (Gen.neg z) * s)) (lde (sem n (Gen.neg z) * s))
        (fun r => if r = z then -wint s r else wint s r) ∧
      lde (sem n (Gen.neg z) * s) = lde s ∧
      oddS (sem n (Gen.neg z) * s) = oddS s := by
  have hcV := isCol_neg (isCol_pcol s) z
  have hoa : Odd ((fun r => if r = z then -wint s r else wint s r) a) := by
    simp only; split_ifs
    · exact odd_neg.2 ((mem_oddS_iff a).1 ha)
    · exact (mem_oddS_iff a).1 ha
  obtain ⟨hpV, hcolV, hkV⟩ := state_gen hs (extent_lt_of_le hs hle) hcV hk hoa
  have hcV' : IsCol (pcol (sem n (Gen.neg z) * s)) (lde (sem n (Gen.neg z) * s))
      (fun r => if r = z then -wint s r else wint s r) := by rw [hcolV, hkV]; exact hcV
  refine ⟨hpV, hcV', hkV, ?_⟩
  ext r
  rw [oddS_eq hcV', mem_oddS_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp

/-- Subcase 2.2.2. -/
theorem squareN_out {s : O_ZHalf n} (hs : s ≠ 1) {z : Fin n}
    (hle : level (sem n (Gen.neg z) * s) ≤ level s) (hk : 0 < lde s)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) (hz : z ∉ [a, b, c, d]) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.neg z) * s)) *
        FreeMonoid.of (Gen.neg z)) (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  obtain ⟨hpV, hcV, hkV, hoV⟩ := stateN hs hle hk ha
  set V := sem n (Gen.neg z) * s
  have hsylls : syll s = Gen.k a b c d hab hbc hcd :: signs s [a, b, c, d] :=
    syll_eq_pos s hU hk hab hbc hcd ha hb hc hd hrest
  have hsyllV : syll V = syll s := by
    rw [hsylls]
    rw [syll_eq_pos V (by rw [hpV]; exact hU) (by rw [hkV]; exact hk) hab hbc hcd
      (hoV ▸ ha) (hoV ▸ hb) (hoV ▸ hc) (hoV ▸ hd) (hoV ▸ hrest)]
    congr 1
    apply signs_congr
    intro r hr
    rw [wint_eq hcV r, if_neg (fun e : r = z => hz (e ▸ hr))]
  refine square_short hs hle [Gen.neg z] (by simp) ?_
  rw [FreeMonoid.ofList_singleton, hsyllV]
  apply comm_list
  intro g hg
  rw [hsylls] at hg
  rcases List.mem_cons.1 hg with rfl | hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    refine (Derivable.of (Table1.r2e z a b c d hab hbc hcd (nodup_vals ?_))).symm
    have := Fin.lt_def.1 hab; have := Fin.lt_def.1 hbc; have := Fin.lt_def.1 hcd
    have h1 : z.val ≠ a.val := fun e => hz.1 (Fin.ext e)
    have h2 : z.val ≠ b.val := fun e => hz.2.1 (Fin.ext e)
    have h3 : z.val ≠ c.val := fun e => hz.2.2.1 (Fin.ext e)
    have h4 : z.val ≠ d.val := fun e => hz.2.2.2 (Fin.ext e)
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    omega
  · obtain ⟨r, _, rfl⟩ := mem_signs hg
    exact neg_comm r z

/-- Subcase 2.2.1: `G` acts on the first odd entry. -/
theorem squareN_in {s : O_ZHalf n} (hs : s ≠ 1) {a : Fin n}
    (hle : level (sem n (Gen.neg a) * s) ≤ level s) (hk : 0 < lde s)
    {b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.neg a) * s)) *
        FreeMonoid.of (Gen.neg a)) (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  obtain ⟨hpV, hcV, hkV, hoV⟩ := stateN hs hle hk ha
  set V := sem n (Gen.neg a) * s
  have hsylls : syll s = Gen.k a b c d hab hbc hcd :: signs s [a, b, c, d] :=
    syll_eq_pos s hU hk hab hbc hcd ha hb hc hd hrest
  have hsyllV : syll V = Gen.k a b c d hab hbc hcd :: signs V [a, b, c, d] :=
    syll_eq_pos V (by rw [hpV]; exact hU) (by rw [hkV]; exact hk) hab hbc hcd
      (hoV ▸ ha) (hoV ▸ hb) (hoV ▸ hc) (hoV ▸ hd) (hoV ▸ hrest)
  have hR : signs V [b, c, d] = signs s [b, c, d] := by
    apply signs_congr
    intro r hr
    have : r ≠ a := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [ne_of_gt hab, ne_of_gt (hab.trans hbc), ne_of_gt (hab.trans (hbc.trans hcd))]
    rw [wint_eq hcV r, if_neg this]
  have hta : tau (wint V a) = !tau (wint s a) := by
    rw [wint_eq hcV a, if_pos rfl]; exact tau_neg ((mem_oddS_iff a).1 ha)
  set R := signs s [b, c, d]
  have hRc : Derivable (Table1 n) (FreeMonoid.ofList R * FreeMonoid.of (Gen.neg a))
      (FreeMonoid.of (Gen.neg a) * FreeMonoid.ofList R) :=
    comm_list (fun g hg => by obtain ⟨r, _, rfl⟩ := mem_signs hg; exact neg_comm r a)
  have hNN : Derivable (Table1 n) (FreeMonoid.of (Gen.neg a) * FreeMonoid.of (Gen.neg a)) 1 :=
    Derivable.of (Table1.r1b a)
  refine square_short hs hle [] (by simp) ?_
  rw [FreeMonoid.ofList_nil, one_mul, hsyllV, hsylls, signs_cons V a [b, c, d],
    signs_cons s a [b, c, d], hR, hta]
  set K := FreeMonoid.of (Gen.k a b c d hab hbc hcd)
  set N := FreeMonoid.of (Gen.neg a)
  cases tau (wint s a)
  · -- `G` adds the sign: `K N_a R N_a ≈ K R`
    simp only [Bool.not_false, ↓reduceIte, List.singleton_append, List.nil_append,
      FreeMonoid.ofList_cons]
    have e1 : Derivable (Table1 n) (K * (N * FreeMonoid.ofList R) * N)
        (K * N * (N * FreeMonoid.ofList R)) :=
      (deq (by simp only [mul_assoc])).trans ((Derivable.refl (K * N)).mul hRc)
    have e2 : Derivable (Table1 n) (K * N * (N * FreeMonoid.ofList R)) (K * FreeMonoid.ofList R) :=
      (deq (by simp only [mul_assoc])).trans
        (((Derivable.refl K).mul (hNN.mul (Derivable.refl (FreeMonoid.ofList R)))).trans
          (deq (by simp)))
    exact e1.trans e2
  · -- `G` removes the sign: `K R N_a ≈ K N_a R`
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.singleton_append,
      FreeMonoid.ofList_cons]
    exact (deq rfl).trans (((Derivable.refl K).mul hRc).trans (deq rfl))

end QCert.LiRossSelinger
