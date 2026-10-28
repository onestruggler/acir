/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Pair confluence

At a state `s` with pivot column at a positive exponent, `H` on a matched
pair (two odd numerators of one class) lowers the level (`lev_pair_lt`).
Two matched pairs `A`, `B` are joined below `s`: there is a word `D` with
`D H_A ≈ H_B` whose every state, from `H_A s` on, is strictly below `s`
(`pair_confluence`).

* `A = B`: `D = ε`.
* `A`, `B` disjoint: `D = H_A H_B`; `H_B` stays a matched pair after `H_A`
  (`pair_keep`), so `H_B H_A s` is below `H_A s` (`lev_two_pairs`).
* `A`, `B` share one index: the three indices are of one class, which has
  an even number of odd entries, so a fourth `d` of the class exists
  (`exists_fourth`); on the window of these four, `D` is the switch from
  `A` to the window's first pair followed by the reverse of the switch
  from `B` (`Switch.lean`).
-/
import QCert.HadamardPi.Switch

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### Matched pairs -/

theorem SameOdd.symm {u w : ℤ√2} (h : SameOdd u w) : SameOdd w u := ⟨h.2.1, h.1, h.2.2.symm⟩

theorem SameOdd.trans {u w y : ℤ√2} (h : SameOdd u w) (h' : SameOdd w y) : SameOdd u y :=
  ⟨h.1, h'.2.1, h.2.2.trans h'.2.2⟩

theorem SameOdd.refl {u : ℤ√2} (h : Odd u.re) : SameOdd u u := ⟨h, h, Iff.rfl⟩

/-- `H` on a matched pair beside another odd entry keeps the exponent and
the other numerators. -/
theorem pair_keep {v : Fin n → ℝ} (hR : InRing v) {p q : Fin n} (hpq : p ≠ q)
    (hs : SameOdd (num v p) (num v q)) {i0 : Fin n} (h0p : i0 ≠ p) (h0q : i0 ≠ q)
    (h0 : Odd (num v i0).re) :
    lde (hv p q v) = lde v ∧ ∀ i, i ≠ p → i ≠ q → num (hv p q v) i = num v i := by
  obtain ⟨hR', hle, -⟩ := pair_reduce hR hpq hs
  have hvi : ∀ i, i ≠ p → i ≠ q → hv p q v i = v i := fun i h1 h2 => by simp [hv, h1, h2]
  have hl : lde (hv p q v) = lde v := by
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    obtain ⟨K, hK⟩ : ∃ K, lde v = K + 1 := ⟨lde v - 1, by omega⟩
    have hden := (denV_lde hR').mono (k' := K) (by omega) i0
    rw [hvi i0 h0p h0q] at hden
    have := toReal_num hR i0
    rw [hK] at this
    exact not_den_of_odd this h0 hden
  refine ⟨hl, fun i h1 h2 => ?_⟩
  simp only [num, hl, hvi i h1 h2]

/-- Two disjoint matched pairs, one after the other. -/
theorem lev_two_pairs {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    {a1 a2 b1 b2 : Fin n} (ha : a1 < a2) (hb : b1 < b2)
    (ha2 : (a2 : ℕ) < piv s) (hb2 : (b2 : ℕ) < piv s)
    (hA : SameOdd (num (col s (pj s (piv_pos hs))) a1) (num (col s (pj s (piv_pos hs))) a2))
    (hB : SameOdd (num (col s (pj s (piv_pos hs))) b1) (num (col s (pj s (piv_pos hs))) b2))
    (h11 : b1 ≠ a1) (h12 : b1 ≠ a2) (h21 : b2 ≠ a1) (h22 : b2 ≠ a2) :
    lev (sem n (Gen.H b1 b2 hb) * (sem n (Gen.H a1 a2 ha) * s)) < lev s := by
  have hp := piv_pos hs
  set v := col s (pj s hp) with hvdef
  have hR : InRing v := col_inRing s _
  obtain ⟨hl, hnum⟩ := pair_keep hR (ne_of_lt ha) hA h11 h12 hB.1
  have hidx : ∀ i ∈ (Gen.H a1 a2 ha).idx, (i : ℕ) < piv s := by
    intro i hi; simp [Gen.idx] at hi; rcases hi with rfl | rfl
    · exact lt_trans (Fin.lt_def.1 ha) ha2
    · exact ha2
  have hk' : lde (hv a1 a2 v) ≠ 0 := by rw [hl]; exact hk
  have hpiv : piv (sem n (Gen.H a1 a2 ha) * s) = piv s :=
    piv_eq_of_col hp hidx (fun h => hk' (by
      rw [show hv a1 a2 v = gv (Gen.H a1 a2 ha) v from rfl, h]
      exact lde_single (Or.inl rfl)))
  have hpu : 0 < piv (sem n (Gen.H a1 a2 ha) * s) := hpiv ▸ hp
  have hcolu : col (sem n (Gen.H a1 a2 ha) * s) (pj _ hpu) = hv a1 a2 v := by
    have : pj _ hpu = pj s hp := Fin.ext (by simp only [pj]; rw [hpiv])
    rw [this]; exact col_sem_mul _ _ _
  have h1 := lev_pair_lt hp ha ha2 hk hA
  have h2 := lev_pair_lt hpu hb (by rw [hpiv]; exact hb2) (by rw [hcolu]; exact hk')
    (by rw [hcolu, hnum b1 h11 h12, hnum b2 h21 h22]; exact hB)
  exact lt_trans h2 h1

/-! ### A fourth entry of the class -/

theorem emod_two_of_iff {x y : ℤ} (h : Odd x ↔ Odd y) : x % 2 = y % 2 := by
  rw [Int.odd_iff, Int.odd_iff] at h
  by_cases hx : x % 2 = 1
  · have := h.1 hx; omega
  · have : ¬y % 2 = 1 := fun hy => hx (h.2 hy)
    omega

open Classical in
/-- The odd entries of one class are evenly many. -/
theorem even_card_class {v : Fin n → ℝ} (hR : InRing v) (hU : IsUnitVec v) (hk : lde v ≠ 0)
    {p : Fin n} (hp : Odd (num v p).re) :
    Even (univ.filter fun i => SameOdd (num v p) (num v i)).card := by
  classical
  have hOO := even_card_odd_odd_num hR hU
  by_cases hpi : Odd (num v p).im
  · have heq : (univ.filter fun i => SameOdd (num v p) (num v i)) =
        univ.filter fun i => Odd (num v i).re ∧ Odd (num v i).im := by
      ext i
      simp only [mem_filter, mem_univ, true_and, SameOdd]
      constructor
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2.1 hpi⟩
      · rintro ⟨h1, h2⟩; exact ⟨hp, h1, ⟨fun _ => h2, fun _ => hpi⟩⟩
    rw [heq]; exact hOO
  · have hO := even_card_oddSet hR hU (Nat.one_le_iff_ne_zero.2 hk)
    have hsub : (univ.filter fun i => Odd (num v i).re ∧ Odd (num v i).im) ⊆ oddSet v := by
      intro i hi; rw [mem_filter] at hi; exact mem_oddSet.2 hi.2.1
    have heq : (univ.filter fun i => SameOdd (num v p) (num v i)) =
        oddSet v \ (univ.filter fun i => Odd (num v i).re ∧ Odd (num v i).im) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_oddSet, SameOdd]
      constructor
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, fun h => hpi (h2.2 h.2)⟩
      · rintro ⟨h1, h2⟩; exact ⟨hp, h1, ⟨fun h => absurd h hpi, fun h => absurd ⟨h1, h⟩ h2⟩⟩
    rw [heq, card_sdiff_of_subset hsub, Nat.even_sub (card_le_card hsub)]
    exact iff_of_true hO hOO

theorem four_of_even {α : Type*} {C : Finset α} (hev : Even C.card) (h3 : 3 ≤ C.card) :
    4 ≤ C.card := by
  obtain ⟨m, hm⟩ := hev; omega

/-- Three entries of one class have a fourth. -/
theorem exists_fourth {v : Fin n → ℝ} (hR : InRing v) (hU : IsUnitVec v) (hk : lde v ≠ 0)
    {p q r : Fin n} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : SameOdd (num v p) (num v q)) (h2 : SameOdd (num v p) (num v r)) :
    ∃ d, d ≠ p ∧ d ≠ q ∧ d ≠ r ∧ SameOdd (num v p) (num v d) := by
  classical
  set C := univ.filter fun i => SameOdd (num v p) (num v i) with hC
  have hev := even_card_class hR hU hk h1.1
  have h3 : ({p, q, r} : Finset (Fin n)) ⊆ C := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rw [hC, mem_filter]
    rcases hi with rfl | rfl | rfl
    · exact ⟨mem_univ _, SameOdd.refl h1.1⟩
    · exact ⟨mem_univ _, h1⟩
    · exact ⟨mem_univ _, h2⟩
  have hc3 : ({p, q, r} : Finset (Fin n)).card = 3 := by
    rw [card_insert_of_notMem (by simp [hpq, hpr]), card_pair hqr]
  have hle := card_le_card h3
  rw [hc3] at hle
  have h4 : 4 ≤ C.card := four_of_even hev hle
  have : (C \ {p, q, r}).Nonempty := by
    rw [← card_pos, card_sdiff_of_subset h3, hc3]; omega
  obtain ⟨d, hd⟩ := this
  rw [mem_sdiff, hC, mem_filter] at hd
  simp only [mem_insert, mem_singleton, not_or] at hd
  exact ⟨d, hd.2.1, hd.2.2.1, hd.2.2.2, hd.1.2⟩

/-! ### Paths backwards -/

theorem PathLt.reverse {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} :
    ∀ {w : List (Gen n)} {t : O n}, PathLt L w t → PathLt L w.reverse (run w t)
  | [], _, h => by simpa using h
  | g :: w, t, h => by
    rw [List.reverse_cons, PathLt.append]
    have hw : run [g] (run (g :: w) t) = run w t := by
      rw [run_cons, run_cons, run_nil, sem_sq_assoc]
    refine ⟨⟨h.2, ?_⟩, ?_⟩
    · rw [hw]; exact h.1.last
    · rw [hw]; exact PathLt.reverse h.1

/-- A word of generators followed by its reverse is the empty word. -/
theorem rev_cancel : ∀ w : List (Gen n), Derivable Fig6 (ofList (w.reverse ++ w)) 1
  | [] => Derivable.refl _
  | g :: w => by
    have hg : Derivable Fig6 (ofList [g, g]) (ofList []) := by
      cases g with
      | Z a => exact Derivable.of (Fig6.a1 a)
      | X a b hab => exact Derivable.of (Fig6.a2 hab)
      | H a b hab => exact Derivable.of (Fig6.a3 hab)
    have e : (g :: w).reverse ++ g :: w = w.reverse ++ [g, g] ++ w := by simp
    rw [e, ofList_append, ofList_append]
    refine (((Derivable.refl (ofList w.reverse)).mul hg).mul (Derivable.refl (ofList w))).trans ?_
    simpa [ofList_append] using rev_cancel w

/-! ### The window of four -/

theorem map_drop_append (f : Fin 4 → Fin n) (hf : StrictMono f) (D : List (Gen 4)) (g : Gen 4)
    (k : ℕ) : (D.map (Gen.map f hf)).drop k ++ [Gen.map f hf g] =
      (D.drop k ++ [g]).map (Gen.map f hf) := by
  rw [List.map_append, List.map_drop]; rfl

section Window

variable {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
  (f : Fin 4 → Fin n) (hf : StrictMono f) (hfJ : ∀ j, (f j : ℕ) < piv s)
  {a b : Fin 4 → ℤ} {c mm par : ℤ}
  (hpat : ∀ j, num (col s (pj s (piv_pos hs))) (f j) = Pat4 a b c j)
  (hsum : a 0 + a 1 + a 2 + a 3 = 2 * mm + par)
include hs hk hfJ hpat hsum

/-- The states of a switch word, from `H_A s`, are below `s`. -/
theorem switch_path {j₁ j₂ : Fin 4} {hj : j₁ < j₂} (S : Switch par j₁ j₂ hj) :
    PathLt (lev s) (S.D.map (Gen.map f hf)) (run [Gen.H (f j₁) (f j₂) (hf hj)] s) := by
  apply pathLt_of_drop
  intro k hkl
  rw [← run_append]
  have := map_drop_append f hf S.D (Gen.H j₁ j₂ hj) k
  simp only [Gen.map] at this
  rw [this]
  exact lev_lt_of_good4 hs hk f hf hfJ hpat hsum (S.good k (by simpa using hkl))

/-- Two pairs of the window are joined below `s`. -/
theorem window_join (hpar : par = 0 ∨ par = 1) {j₁ j₂ k₁ k₂ : Fin 4} (hj : j₁ < j₂)
    (hk' : k₁ < k₂) :
    ∃ D : List (Gen n),
      Derivable Fig6 (ofList (D ++ [Gen.H (f j₁) (f j₂) (hf hj)]))
        (ofList [Gen.H (f k₁) (f k₂) (hf hk')]) ∧
      PathLt (lev s) D (run [Gen.H (f j₁) (f j₂) (hf hj)] s) := by
  obtain ⟨SA⟩ := switch4 j₁ j₂ hj par hpar
  obtain ⟨SB⟩ := switch4 k₁ k₂ hk' par hpar
  set gm := Gen.map f hf
  have dA := der_map f hf SA.der
  have dB := der_map f hf SB.der
  simp only [List.map_append, List.map_cons, List.map_nil] at dA dB
  refine ⟨(SB.D.map gm).reverse ++ SA.D.map gm, ?_, ?_⟩
  · -- `Bʳ A H_A ≈ Bʳ H₀₁ ≈ Bʳ B H_B ≈ H_B`
    rw [List.append_assoc, ofList_append]
    refine ((Derivable.refl _).mul dA).trans ?_
    refine ((Derivable.refl _).mul dB.symm).trans ?_
    rw [← ofList_append, ← List.append_assoc, ofList_append]
    simpa using (rev_cancel (SB.D.map gm)).mul (Derivable.refl (ofList [gm (Gen.H k₁ k₂ hk')]))
  · rw [PathLt.append]
    have pA := switch_path hs hk f hf hfJ hpat hsum SA
    have pB := switch_path hs hk f hf hfJ hpat hsum SB
    refine ⟨pA, ?_⟩
    have e1 : run (SA.D.map gm) (run [Gen.H (f j₁) (f j₂) (hf hj)] s) =
        run (SB.D.map gm) (run [Gen.H (f k₁) (f k₂) (hf hk')] s) := by
      rw [← run_append, ← run_append]
      exact (run_eq_of_der dA s).trans (run_eq_of_der dB s).symm
    rw [e1]
    exact pB.reverse

end Window

theorem Gen.H_eq {a b a' b' : Fin n} {h : a < b} {h' : a' < b'} (ea : a = a') (eb : b = b') :
    Gen.H a b h = Gen.H a' b' h' := by
  subst ea eb; rfl

/-- The numerators of a window of four odd entries of one class, as a
pattern. -/
theorem window_pattern {v : Fin n → ℝ} (f : Fin 4 → Fin n)
    (hodd : ∀ j, SameOdd (num v (f 0)) (num v (f j))) :
    ∃ (a b : Fin 4 → ℤ) (c mm par : ℤ), (∀ j, num v (f j) = Pat4 a b c j) ∧
      a 0 + a 1 + a 2 + a 3 = 2 * mm + par ∧ (par = 0 ∨ par = 1) := by
  refine ⟨fun j => ((num v (f j)).re - 1) / 2, fun j => ((num v (f j)).im - (num v (f 0)).im) / 2,
    (num v (f 0)).im,
    (((num v (f 0)).re - 1) / 2 + ((num v (f 1)).re - 1) / 2 + ((num v (f 2)).re - 1) / 2 +
      ((num v (f 3)).re - 1) / 2) / 2,
    (((num v (f 0)).re - 1) / 2 + ((num v (f 1)).re - 1) / 2 + ((num v (f 2)).re - 1) / 2 +
      ((num v (f 3)).re - 1) / 2) % 2, fun j => ?_, by dsimp only; omega, by omega⟩
  have h1 := Int.odd_iff.1 (hodd j).2.1
  have h2 := emod_two_of_iff (hodd j).2.2
  apply Zsqrtd.ext
  · simp only [Pat4_re]; omega
  · simp only [Pat4_im]; omega

/-- Two matched pairs are joined below `s`. -/
theorem pair_confluence {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    {a1 a2 b1 b2 : Fin n} (ha : a1 < a2) (hb : b1 < b2)
    (ha2 : (a2 : ℕ) < piv s) (hb2 : (b2 : ℕ) < piv s)
    (hA : SameOdd (num (col s (pj s (piv_pos hs))) a1) (num (col s (pj s (piv_pos hs))) a2))
    (hB : SameOdd (num (col s (pj s (piv_pos hs))) b1) (num (col s (pj s (piv_pos hs))) b2)) :
    ∃ D : List (Gen n), Derivable Fig6 (ofList (D ++ [Gen.H a1 a2 ha])) (ofList [Gen.H b1 b2 hb]) ∧
      PathLt (lev s) D (run [Gen.H a1 a2 ha] s) := by
  classical
  have hp := piv_pos hs
  set v := col s (pj s hp) with hvdef
  have hR : InRing v := col_inRing s _
  have hU : IsUnitVec v := col_unit s _
  have hrun1 : ∀ g : Gen n, run [g] s = sem n g * s := fun g => by rw [run_cons, run_nil]
  have hlA : lev (run [Gen.H a1 a2 ha] s) < lev s := by
    rw [hrun1]; exact lev_pair_lt hp ha ha2 hk hA
  have hlB : lev (run [Gen.H b1 b2 hb] s) < lev s := by
    rw [hrun1]; exact lev_pair_lt hp hb hb2 hk hB
  -- `A = B`
  by_cases heq : a1 = b1 ∧ a2 = b2
  · obtain ⟨rfl, rfl⟩ := heq
    exact ⟨[], Derivable.refl _, hlA⟩
  -- `A`, `B` disjoint
  by_cases hdis : b1 ≠ a1 ∧ b1 ≠ a2 ∧ b2 ≠ a1 ∧ b2 ≠ a2
  · obtain ⟨h11, h12, h21, h22⟩ := hdis
    have hder : Derivable Fig6 (ofList ([Gen.H a1 a2 ha, Gen.H b1 b2 hb] ++ [Gen.H a1 a2 ha]))
        (ofList [Gen.H b1 b2 hb]) :=
      (rw_at [Gen.H a1 a2 ha, Gen.H b1 b2 hb, Gen.H a1 a2 ha] 1
        (rl_b6 hb ha h11 h12 h21 h22) rfl).trans (rw_at _ 0 (rl_a3 ha) rfl)
    refine ⟨[Gen.H a1 a2 ha, Gen.H b1 b2 hb], hder, ⟨⟨hlA, ?_⟩, ?_⟩⟩
    · rw [hrun1, run_cons, run_nil]
      exact lev_two_pairs hs hk ha hb ha2 hb2 hA hB h11 h12 h21 h22
    · rw [← run_append, run_eq_of_der hder]; exact hlB
  -- `A`, `B` share one index `e`
  have ha1 : (a1 : ℕ) < piv s := lt_trans (Fin.lt_def.1 ha) ha2
  have hb1 : (b1 : ℕ) < piv s := lt_trans (Fin.lt_def.1 hb) hb2
  obtain ⟨e, he1, he2, heA, hBe1, hBe2, hecls⟩ : ∃ e : Fin n, e ≠ a1 ∧ e ≠ a2 ∧ (e : ℕ) < piv s ∧
      (b1 = e ∨ b1 = a1 ∨ b1 = a2) ∧ (b2 = e ∨ b2 = a1 ∨ b2 = a2) ∧
        SameOdd (num v a1) (num v e) := by
    by_cases hb1A : b1 = a1 ∨ b1 = a2
    · have hb2A : b2 ≠ a1 ∧ b2 ≠ a2 := by
        rcases hb1A with rfl | rfl
        · exact ⟨ne_of_gt hb, fun h => heq ⟨rfl, h.symm⟩⟩
        · exact ⟨ne_of_gt (lt_trans ha hb), ne_of_gt hb⟩
      refine ⟨b2, hb2A.1, hb2A.2, hb2, Or.inr hb1A, Or.inl rfl, ?_⟩
      rcases hb1A with rfl | rfl
      · exact hB
      · exact hA.trans hB
    · push Not at hb1A
      have hb2A : b2 = a1 ∨ b2 = a2 := by
        by_contra h; push Not at h; exact hdis ⟨hb1A.1, hb1A.2, h.1, h.2⟩
      refine ⟨b1, hb1A.1, hb1A.2, hb1, Or.inl rfl, Or.inr hb2A, ?_⟩
      rcases hb2A with rfl | rfl
      · exact hB.symm
      · exact hA.trans hB.symm
  obtain ⟨d, hd1, hd2, hde, hdcls⟩ := exists_fourth hR hU hk (ne_of_lt ha) (Ne.symm he1)
    (Ne.symm he2) hA hecls
  have hdJ : (d : ℕ) < piv s := pcol_low hp (ne_zero_of_odd hR hdcls.2.1)
  set W : Finset (Fin n) := {a1, a2, e, d} with hW
  have hWc : W.card = 4 := by
    rw [hW, card_insert_of_notMem (by simp [ne_of_lt ha, he1.symm, hd1.symm]),
      card_insert_of_notMem (by simp [he2.symm, hd2.symm]), card_pair hde.symm]
  set f := W.orderEmbOfFin hWc
  have hf : StrictMono f := f.strictMono
  have hfW : ∀ j, f j ∈ W := fun j => W.orderEmbOfFin_mem hWc j
  have hWf : ∀ x ∈ W, ∃ j, f j = x := by
    intro x hx
    have : x ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hx
    exact this
  have hmem : ∀ x, x ∈ W ↔ x = a1 ∨ x = a2 ∨ x = e ∨ x = d := by
    intro x; simp [hW]
  have hcls : ∀ x ∈ W, SameOdd (num v a1) (num v x) := by
    intro x hx
    rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
    · exact SameOdd.refl hA.1
    · exact hA
    · exact hecls
    · exact hdcls
  have hfJ : ∀ j, (f j : ℕ) < piv s := by
    intro j
    rcases (hmem (f j)).1 (hfW j) with h | h | h | h <;> rw [h]
    exacts [ha1, ha2, heA, hdJ]
  obtain ⟨a, b, c, mm, par, hpat, hsum, hpar⟩ := window_pattern (v := v) f
    (fun j => (hcls _ (hfW 0)).symm.trans (hcls _ (hfW j)))
  have hb1W : b1 ∈ W := by
    rw [hmem]; rcases hBe1 with h | h | h <;> simp [h]
  have hb2W : b2 ∈ W := by
    rw [hmem]; rcases hBe2 with h | h | h <;> simp [h]
  obtain ⟨j1, hj1⟩ := hWf a1 (by rw [hmem]; simp)
  obtain ⟨j2, hj2⟩ := hWf a2 (by rw [hmem]; simp)
  obtain ⟨k1, hk1⟩ := hWf b1 hb1W
  obtain ⟨k2, hk2⟩ := hWf b2 hb2W
  have hj : j1 < j2 := hf.lt_iff_lt.1 (by rw [hj1, hj2]; exact ha)
  have hkk : k1 < k2 := hf.lt_iff_lt.1 (by rw [hk1, hk2]; exact hb)
  obtain ⟨D, hD, hPD⟩ := window_join hs hk f hf hfJ hpat hsum hpar hj hkk
  rw [Gen.H_eq hj1 hj2 (h' := ha), Gen.H_eq hk1 hk2 (h' := hb)] at hD
  rw [Gen.H_eq hj1 hj2 (h' := ha)] at hPD
  exact ⟨D, hD, hPD⟩

end QCert.HadamardPi
