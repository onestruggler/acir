/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Main Case 9 (2)(b) with exactly four odd entries: Clément's Case 3.4

The state `s` has exactly four odd numerators: `0` and `1` of different
classes, `P` (the partner of `0`, the first syllable being `H_[0,P]`) and
`Q` (the partner of `1`).  The first syllable of `r = H_[0,1] s` is
`H_[0,P']` with `P' ∈ {P, Q}`.  The square is closed by a join of
`H_[1,Q] H_[0,P]` and `H_[1,Q''] H_[0,P'] H_[0,1]` (`Join.extend`), `Q''` the
other of `P`, `Q`.  Two transpositions move `P` to `2` and `Q` to `3`
(`move_opt`, Clément's "up to a renaming of indices"), conjugating the words;
the resulting state is an entry of the case analysis of `Case34.lean`, for
the class `ε` of `0` and whether `P' = P` (Clément's `η = ε`).
-/
import QCert.HadamardPi.Case34

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### Moving an entry by a transposition -/

/-- Rename the second index of `H_[x,y]` by the transposition of `p`, `c`. -/
def swapG (p c : Fin n) : Gen n → Gen n
  | .H x y h => if h' : x < Equiv.swap p c y then .H x (Equiv.swap p c y) h' else .H x y h
  | g => g

/-- `H_[x,y]` with `x ≤ 1`. -/
def LowH (g : Gen n) : Prop := ∃ x y h, g = Gen.H x y h ∧ (x : ℕ) ≤ 1

theorem swap_gt {p c x y : Fin n} (hpc : p ≤ c) (hp : 2 ≤ (p : ℕ)) (hx : (x : ℕ) ≤ 1)
    (hxy : x < y) : x < Equiv.swap p c y := by
  rw [Equiv.swap_apply_def]
  have := Fin.lt_def.1 hxy
  have := Fin.le_def.1 hpc
  split_ifs <;> simp only [Fin.lt_def] <;> omega

theorem swapG_H {p c x y : Fin n} (hpc : p ≤ c) (hp : 2 ≤ (p : ℕ)) (hx : (x : ℕ) ≤ 1)
    (hxy : x < y) :
    swapG p c (Gen.H x y hxy) = Gen.H x (Equiv.swap p c y) (swap_gt hpc hp hx hxy) := by
  simp only [swapG, dif_pos (swap_gt hpc hp hx hxy)]

theorem conj_H {p c x y : Fin n} (hpc : p < c) (hp : 2 ≤ (p : ℕ)) (hx : (x : ℕ) ≤ 1)
    (hxy : x < y) :
    Derivable Fig6 (ofList [swapG p c (Gen.H x y hxy), Gen.X p c hpc])
      (ofList [Gen.X p c hpc, Gen.H x y hxy]) := by
  have hxp : x < p := Fin.lt_def.2 (by omega)
  rw [swapG_H hpc.le hp hx hxy]
  by_cases hyp : y = p
  · subst hyp
    have e : Equiv.swap y c y = c := Equiv.swap_apply_left y c
    have := (Derivable.of (Fig6.c5 hxp hpc) : Derivable Fig6 _ _)
    rw [show Gen.H x (Equiv.swap y c y) (swap_gt hpc.le hp hx hxy) = Gen.H x c (hxp.trans hpc)
      from Gen.H_eq rfl e]
    exact this
  by_cases hyc : y = c
  · subst hyc
    rw [show Gen.H x (Equiv.swap p y y) (swap_gt hpc.le hp hx hxy) = Gen.H x p hxp
      from Gen.H_eq rfl (Equiv.swap_apply_right p y)]
    -- `H_[x,p] X ≈ X X H_[x,p] X ≈ X H_[x,y] X X ≈ X H_[x,y]`, by (c5)
    have c5 : Derivable Fig6 (ofList [Gen.H x y hxy, Gen.X p y hpc])
        (ofList [Gen.X p y hpc, Gen.H x p hxp]) := Derivable.of (Fig6.c5 hxp hpc)
    have e1 := der_mid [] [] [Gen.H x p hxp, Gen.X p y hpc] [Gen.X p y hpc, Gen.X p y hpc]
      (rl_a2 hpc).symm
    have e2 := der_mid [Gen.X p y hpc] [Gen.X p y hpc, Gen.H x p hxp] [Gen.X p y hpc]
      [Gen.H x y hxy, Gen.X p y hpc] c5.symm
    have e3 := der_mid [Gen.X p y hpc, Gen.H x y hxy] [Gen.X p y hpc, Gen.X p y hpc] []
      [] (rl_a2 hpc)
    simp only [List.nil_append, List.append_nil, List.cons_append] at e1 e2 e3
    exact e1.trans (e2.trans e3)
  · rw [show Gen.H x (Equiv.swap p c y) (swap_gt hpc.le hp hx hxy) = Gen.H x y hxy
      from Gen.H_eq rfl (Equiv.swap_apply_of_ne_of_ne hyp hyc)]
    have hpx : p ≠ x := fun h => by rw [h] at hxp; exact lt_irrefl _ hxp
    have hcx : c ≠ x := fun h => by rw [h] at hpc; exact lt_asymm hpc hxp
    exact (rl_b5 hpc hxy hpx (Ne.symm hyp) hcx (Ne.symm hyc)).symm

theorem conj_list {p c : Fin n} (hpc : p < c) (hp : 2 ≤ (p : ℕ)) :
    ∀ A : List (Gen n), (∀ g ∈ A, LowH g) →
      Derivable Fig6 (ofList (A.map (swapG p c) ++ [Gen.X p c hpc]))
        (ofList ([Gen.X p c hpc] ++ A))
  | [], _ => Derivable.refl _
  | g :: A, h => by
    obtain ⟨x, y, hxy, rfl, hx⟩ := h g List.mem_cons_self
    have ih := conj_list hpc hp A fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    have e1 := der_mid [swapG p c (Gen.H x y hxy)] (A.map (swapG p c) ++ [Gen.X p c hpc]) []
      ([Gen.X p c hpc] ++ A) ih
    have e2 := der_mid [] [swapG p c (Gen.H x y hxy), Gen.X p c hpc] A
      [Gen.X p c hpc, Gen.H x y hxy] (conj_H hpc hp hx hxy)
    simp only [List.map_cons, List.nil_append, List.append_nil, List.cons_append] at e1 e2 ⊢
    exact e1.trans e2

theorem swapG2_H {p c p' c' x y x' y' : Fin n} (hpc : p ≤ c) (hp : 2 ≤ (p : ℕ))
    (hpc' : p' ≤ c') (hp' : 2 ≤ (p' : ℕ)) (hx : (x : ℕ) ≤ 1) (hxy : x < y) (h' : x' < y')
    (ex : x = x') (ey : Equiv.swap p' c' (Equiv.swap p c y) = y') :
    swapG p' c' (swapG p c (Gen.H x y hxy)) = Gen.H x' y' h' := by
  rw [swapG_H hpc hp hx hxy, swapG_H hpc' hp' hx]
  exact Gen.H_eq ex ey

theorem swapG_self (p : Fin n) (hp : 2 ≤ (p : ℕ)) :
    ∀ A : List (Gen n), (∀ g ∈ A, LowH g) → A.map (swapG p p) = A
  | [], _ => rfl
  | g :: A, h => by
    obtain ⟨x, y, hxy, rfl, hx⟩ := h g List.mem_cons_self
    rw [List.map_cons, swapG_self p hp A fun g' hg' => h g' (List.mem_cons_of_mem _ hg'),
      swapG_H le_rfl hp hx hxy]
    congr 1
    exact Gen.H_eq rfl (Equiv.swap_self p ▸ rfl)

theorem lowH_map {p c : Fin n} (hpc : p ≤ c) (hp : 2 ≤ (p : ℕ)) {A : List (Gen n)}
    (h : ∀ g ∈ A, LowH g) : ∀ g ∈ A.map (swapG p c), LowH g := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨x, y, hxy, rfl, hx⟩ := h g0 hg0
  rw [swapG_H hpc hp hx hxy]
  exact ⟨x, _, _, rfl, hx⟩

/-- A transposition of `p ≤ c` (none if `p = c`): a join at the moved state,
with the words renamed, gives one at `s`. -/
theorem move_opt {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    {p c : Fin n} (hpc : p ≤ c) (hp : 2 ≤ (p : ℕ)) (hcJ : (c : ℕ) < piv s)
    {A B : List (Gen n)} (hA : ∀ g ∈ A, LowH g) (hB : ∀ g ∈ B, LowH g)
    (hσ : lev (run A s) < lev s) (hρ : lev (run B s) < lev s) {i0 : Fin n}
    (hi0 : i0 ≠ p ∧ i0 ≠ c) (hodd : Odd (num (col s (pj s (piv_pos hs))) i0).re)
    (hJ : ∀ (s' : O n) (hs' : s' ≠ 1),
      lde (col s' (pj s' (piv_pos hs'))) = lde (col s (pj s (piv_pos hs))) → piv s' = piv s →
      (∀ i, num (col s' (pj s' (piv_pos hs'))) i =
        num (col s (pj s (piv_pos hs))) (Equiv.swap p c i)) →
      lev (run (A.map (swapG p c)) s') < lev s' → lev (run (B.map (swapG p c)) s') < lev s' →
      Join s' (A.map (swapG p c)) (B.map (swapG p c))) :
    Join s A B := by
  classical
  rcases eq_or_lt_of_le hpc with rfl | hlt
  · have := hJ s hs rfl rfl (fun i => by rw [Equiv.swap_self, Equiv.refl_apply])
      (by rwa [swapG_self p hp A hA]) (by rwa [swapG_self p hp B hB])
    rwa [swapG_self p hp A hA, swapG_self p hp B hB] at this
  · set v := col s (pj s (piv_pos hs))
    have hpJ : (p : ℕ) < piv s := lt_trans (Fin.lt_def.1 hlt) hcJ
    set K := [Gen.X p c hlt]
    have hKi : ∀ g ∈ K, ∀ i ∈ g.idx, (i : ℕ) < piv s := by
      intro g hg i hi
      simp only [K, List.mem_singleton] at hg; subst hg
      simp only [Gen.idx, mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hpJ
      · exact hcJ
    have hsw : ∀ i, scw K (num v) i = num v (Equiv.swap p c i) := by
      intro i
      simp only [K, scw, scg, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    have hodd' : Odd (num v (Equiv.swap p c i0)).re := by
      rw [Equiv.swap_apply_of_ne_of_ne hi0.1 hi0.2]; exact hodd
    obtain ⟨hs', hpiv, hl, hnum⟩ := state_after hs hk hKi
      (U := fun i => num v (Equiv.swap p c i)) (fun i => by
        beta_reduce; rw [← hsw i]; simp only [hcntw, hcnt, K, pow_zero, one_mul, add_zero]; rfl)
      hodd'
    have hlev0 : ∀ g ∈ K, ∀ i ∈ g.idx, lev0 i < lev s := fun g hg i hi =>
      lev0_lt_of_lde (piv_pos hs) (hKi g hg i hi) hk
    -- the transposition keeps the level
    have hlevK : lev (run K s) = lev s := by
      have hoS : oddSet (col (run K s) (pj _ (piv_pos hs'))) = (oddSet v).map (Equiv.swap p c).toEmbedding := by
        ext i
        rw [mem_oddSet, hnum, Finset.mem_map_equiv, mem_oddSet, Equiv.symm_swap]
      have hkl : kl (col (run K s) (pj _ (piv_pos hs'))) = kl v := by
        unfold kl; rw [hl, hoS, Finset.card_map]
      rw [lev, lev, pcol_eq (piv_pos hs'), pcol_eq (piv_pos hs), hkl, hpiv]
    have hstep : ∀ t : O n, lev t < lev s → lev (run K t) < lev s := by
      intro t ht
      simp only [K, run_cons, run_nil]
      exact lt_of_le_of_lt (lev_X_le_max hlt)
        (max_lt ht (hlev0 (Gen.X p c hlt) (List.mem_singleton_self _) c (by simp [Gen.idx])))
    refine Join.transfer (m := K) (μ := K) (ν := K) (A' := A.map (swapG p c))
      (B' := B.map (swapG p c)) (fun g hg => ⟨by simp [K] at hg; subst hg; trivial,
        fun i hi => le_of_lt (hlev0 g hg i hi)⟩)
      (fun g hg => ⟨by simp [K] at hg; subst hg; trivial, hlev0 g hg⟩)
      (fun g hg => ⟨by simp [K] at hg; subst hg; trivial, hlev0 g hg⟩)
      (conj_list hlt hp A hA) (conj_list hlt hp B hB) hσ
      (hJ _ hs' hl hpiv hnum (by
        rw [← run_append, run_eq_of_der (conj_list hlt hp A hA), run_append]
        rw [show lev (run K s) = lev s from hlevK]
        exact hstep _ hσ) (by
        rw [← run_append, run_eq_of_der (conj_list hlt hp B hB), run_append]
        rw [show lev (run K s) = lev s from hlevK]
        exact hstep _ hρ))

/-! ### The fourth odd entry -/

theorem four_odd {v : Fin n → ℝ} (hR : InRing v) (hU : IsUnitVec v) (hk : lde v ≠ 0)
    {z o P : Fin n} (ho : Odd (num v o).re) (hzo : ¬SameOdd (num v z) (num v o))
    (hzP : z ≠ P) (hP : SameOdd (num v z) (num v P)) (hl : (oddSet v).card = 4) :
    ∃ Q, Q ≠ z ∧ Q ≠ o ∧ Q ≠ P ∧ SameOdd (num v o) (num v Q) ∧ oddSet v = {z, o, P, Q} := by
  classical
  have hev := even_card_class hR hU hk ho
  have hoC : o ∈ univ.filter fun i => SameOdd (num v o) (num v i) := by
    simp only [mem_filter, mem_univ, true_and]; exact SameOdd.refl ho
  have h2 : 1 < (univ.filter fun i => SameOdd (num v o) (num v i)).card := by
    have := card_pos.2 ⟨o, hoC⟩
    obtain ⟨r, hr⟩ := hev
    omega
  obtain ⟨Q, hQ, hQo⟩ := Finset.exists_mem_ne h2 o
  simp only [mem_filter, mem_univ, true_and] at hQ
  have hz : Odd (num v z).re := hP.1
  have hQz : Q ≠ z := by rintro rfl; exact hzo hQ.symm
  have hQP : Q ≠ P := by rintro rfl; exact hzo (hP.trans hQ.symm)
  have hoz : o ≠ z := by rintro rfl; exact hzo (SameOdd.refl ho)
  have hoP : o ≠ P := by rintro rfl; exact hzo hP
  refine ⟨Q, hQz, hQo, hQP, hQ, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rw [mem_oddSet]
    rcases hi with rfl | rfl | rfl | rfl
    · exact hz
    · exact ho
    · exact hP.2.1
    · exact hQ.2.1
  · rw [hl, card_insert_of_notMem (by simp [Ne.symm hoz, hzP, Ne.symm hQz]),
      card_insert_of_notMem (by simp [hoP, Ne.symm hQo]),
      card_insert_of_notMem (by simp [Ne.symm hQP]), card_singleton]


/-! ### The entries of the case tree -/

/-- The parameters of the four odd entries. -/
def tP0 (u : Fin 4 → ℤ√2) (e : ℤ) : ℕ → ℤ := fun i =>
  [((u 0).re - 1) / 2, ((u 0).im - e) / 2, ((u 1).re - 1) / 2, ((u 1).im - (1 - e)) / 2,
    ((u 2).re - 1) / 2, ((u 2).im - e) / 2, ((u 3).re - 1) / 2, ((u 3).im - (1 - e)) / 2].getD i 0

theorem winPat_P0 {s : O n} {hs : s ≠ 1} {hw : 4 ≤ piv s} {u : Fin 4 → ℤ√2}
    (hu : ∀ j, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) = u j)
    (ho : ∀ j, Odd (u j).re) (ε : Bool)
    (hc : ∀ j : Fin 4, Odd (u j).im ↔ (decide ((j : ℕ) % 2 = 0) = ε)) :
    WinPat s hs hw (if ε then c34_P0_1 else c34_P0_0) (tP0 u (if ε then 1 else 0)) := by
  have hm : ∀ j : Fin 4, (u j).im % 2 = if decide ((j : ℕ) % 2 = 0) = ε then 1 else 0 := by
    intro j
    have := hc j
    split_ifs with h
    · exact Int.odd_iff.1 (this.2 h)
    · have h' : ¬Odd (u j).im := fun h'' => h (this.1 h'')
      rw [Int.not_odd_iff_even, Int.even_iff] at h'; exact h'
  have hr : ∀ j : Fin 4, (u j).re % 2 = 1 := fun j => Int.odd_iff.1 (ho j)
  have r0 := hr 0; have r1 := hr 1; have r2 := hr 2; have r3 := hr 3
  have m0 := hm 0; have m1 := hm 1; have m2 := hm 2; have m3 := hm 3
  intro j
  rw [hu j]
  cases ε <;> simp at m0 m1 m2 m3 <;> fin_cases j <;>
    (apply Zsqrtd.ext <;> simp [c34_P0_0, c34_P0_1, c34_p253, c34_p255, zev, evv, c1, tP0] <;> omega)

theorem eta_P0 (u : Fin 4 → ℤ√2) (e : ℤ) (h0 : Odd (u 0).re) (h1 : Odd (u 1).re) :
    evv [1, 1, 0, 1, 0, 0, 0, 0, 0] (c1 (tP0 u e)) = ((u 0).re + (u 1).re) / 2 := by
  obtain ⟨r0, hr0⟩ := h0
  obtain ⟨r1, hr1⟩ := h1
  simp [evv, c1, tP0]
  omega

/-- The four odd entries at `0, 1, 2, 3`, with classes `ε`, `1 - ε`, `ε`,
`1 - ε`, the other entries even: the joins of the case tree, for `η = ε`
and `η ≠ ε`, `η` the parity of `(u₀ + u₁) / 2`. -/
theorem entry_join {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : 4 ≤ piv s) (htail : TailD s hs 4 1) {u : Fin 4 → ℤ√2}
    (hu : ∀ j, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) = u j)
    (ho : ∀ j, Odd (u j).re) (ε : Bool)
    (hc : ∀ j : Fin 4, Odd (u j).im ↔ (decide ((j : ℕ) % 2 = 0) = ε)) :
    (((u 0).re + (u 1).re) / 2 % 2 = (if ε then 1 else 0) →
      wJ s hw ([hL 1 3, hL 0 2] : List (Gen 4)) ([hL 1 3, hL 0 2, hL 0 1] : List (Gen 4))) ∧
    (((u 0).re + (u 1).re) / 2 % 2 = (if ε then 0 else 1) →
      wJ s hw ([hL 1 3, hL 0 2] : List (Gen 4)) ([hL 1 2, hL 0 3, hL 0 1] : List (Gen 4))) := by
  have hP := winPat_P0 (hs := hs) (hw := hw) hu ho ε hc
  have hη := eta_P0 u (if ε then 1 else 0) (ho 0) (ho 1)
  cases ε with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hP hη ⊢
    exact ⟨fun h => c34_entryE0 s hs hk hw _ hP htail (by rw [hη]; exact h),
      fun h => c34_entryN0 s hs hk hw _ hP htail (by rw [hη]; exact h)⟩
  | true =>
    simp only [if_true] at hP hη ⊢
    exact ⟨fun h => c34_entryE1 s hs hk hw _ hP htail (by rw [hη]; exact h),
      fun h => c34_entryN1 s hs hk hw _ hP htail (by rw [hη]; exact h)⟩

/-! ### Main Case 9 (2)(b) with four odd entries -/

theorem lowH_pair {x y : Fin n} (h : x < y) (hx : (x : ℕ) ≤ 1) : LowH (Gen.H x y h) :=
  ⟨x, y, h, rfl, hx⟩

theorem swap_far {p c i : Fin n} (h1 : (i : ℕ) ≠ p) (h2 : (i : ℕ) ≠ c) : Equiv.swap p c i = i :=
  Equiv.swap_apply_of_ne_of_ne (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))

/-- The end of the sorting: the entry of the case tree at `s₂`, whose entries
are those of `s` along `τ = (2 P) ∘ (3 Q₁)`. -/
theorem sorted_join {s s₂ : O n} (hs : s ≠ 1) (hs₂ : s₂ ≠ 1)
    (hk₂ : lde (col s₂ (pj s₂ (piv_pos hs₂))) ≠ 0) (h4 : 4 ≤ piv s₂)
    {z o P Q : Fin n} (τ : Equiv.Perm (Fin n))
    (hnum : ∀ i, num (col s₂ (pj s₂ (piv_pos hs₂))) i = num (col s (pj s (piv_pos hs))) (τ i))
    (hτ : ∀ j : Fin 4, τ (Fin.castLE (h4.trans (piv_le_n s₂)) j) = ![z, o, P, Q] j)
    (hset : oddSet (col s (pj s (piv_pos hs))) = {z, o, P, Q})
    (h0 : Odd (num (col s (pj s (piv_pos hs))) z).re)
    (hzo : ¬SameOdd (num (col s (pj s (piv_pos hs))) z) (num (col s (pj s (piv_pos hs))) o))
    (h1 : Odd (num (col s (pj s (piv_pos hs))) o).re)
    (hzP : SameOdd (num (col s (pj s (piv_pos hs))) z) (num (col s (pj s (piv_pos hs))) P))
    (hoQ : SameOdd (num (col s (pj s (piv_pos hs))) o) (num (col s (pj s (piv_pos hs))) Q)) :
    let u := ![num (col s (pj s (piv_pos hs))) z, num (col s (pj s (piv_pos hs))) o,
      num (col s (pj s (piv_pos hs))) P, num (col s (pj s (piv_pos hs))) Q]
    ((Odd (((u 0).re + (u 1).re) / 2) ↔ Odd (u 0).im) →
      wJ s₂ h4 ([hL 1 3, hL 0 2] : List (Gen 4)) ([hL 1 3, hL 0 2, hL 0 1] : List (Gen 4))) ∧
    ((Odd (((u 0).re + (u 1).re) / 2) ↔ ¬Odd (u 0).im) →
      wJ s₂ h4 ([hL 1 3, hL 0 2] : List (Gen 4)) ([hL 1 2, hL 0 3, hL 0 1] : List (Gen 4))) := by
  intro u
  set v := col s (pj s (piv_pos hs))
  have hu : ∀ j, num (col s₂ (pj s₂ (piv_pos hs₂))) (Fin.castLE (h4.trans (piv_le_n s₂)) j) = u j := by
    intro j; rw [hnum, hτ]; fin_cases j <;> rfl
  have ho : ∀ j, Odd (u j).re := by
    intro j; fin_cases j
    · exact h0
    · exact h1
    · exact hzP.2.1
    · exact hoQ.2.1
  have hdiff : ¬(Odd (num v z).im ↔ Odd (num v o).im) := fun h => hzo ⟨h0, h1, h⟩
  set ε := decide (Odd (num v z).im) with hε
  have hc : ∀ j : Fin 4, Odd (u j).im ↔ (decide ((j : ℕ) % 2 = 0) = ε) := by
    intro j; fin_cases j
    · show Odd (num v z).im ↔ _; simp [hε]
    · show Odd (num v o).im ↔ _; simp only [hε]; by_cases h : Odd (num v z).im <;> simp [h] at hdiff ⊢ <;> tauto
    · show Odd (num v P).im ↔ _; rw [← hzP.2.2]; simp [hε]
    · show Odd (num v Q).im ↔ _; rw [← hoQ.2.2]; simp only [hε]
      by_cases h : Odd (num v z).im <;> simp [h] at hdiff ⊢ <;> tauto
  -- the entries outside the window are even
  have htail : TailD s₂ hs₂ 4 1 := by
    intro i hi
    rw [hnum]
    have hne : τ i ∉ ({z, o, P, Q} : Finset (Fin n)) := by
      intro hm
      simp only [mem_insert, mem_singleton] at hm
      have key : ∀ j : Fin 4, τ i = ![z, o, P, Q] j → False := by
        intro j hj
        rw [← hτ j] at hj
        have := congrArg Fin.val (τ.injective hj)
        simp at this
        omega
      rcases hm with h | h | h | h
      · exact key 0 h
      · exact key 1 h
      · exact key 2 h
      · exact key 3 h
    have hev : ¬Odd (num v (τ i)).re := by
      intro h; apply hne; rw [← hset, mem_oddSet]; exact h
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨r, hr⟩ := hev
    exact ⟨⟨(num v (τ i)).im, r⟩, by rw [pow_one, rt2_mul]; ext <;> simp <;> omega⟩
  have hE := entry_join hs₂ hk₂ h4 htail hu ho ε hc
  have hmod : ∀ x : ℤ, (x % 2 = (if ε then 1 else 0) ↔ (Odd x ↔ ε = true)) := by
    intro x; cases ε <;> simp [Int.odd_iff]
  have hmod' : ∀ x : ℤ, (x % 2 = (if ε then 0 else 1) ↔ (Odd x ↔ ε = false)) := by
    intro x; cases ε <;> simp [Int.odd_iff]
  refine ⟨fun h => hE.1 ((hmod _).2 ?_), fun h => hE.2 ((hmod' _).2 ?_)⟩
  · rw [h]; show Odd (num v z).im ↔ _; simp [hε]
  · rw [h]; show ¬Odd (num v z).im ↔ _; simp [hε]

theorem case9_four : Case9Four n := by
  intro s hs z o hzo hz ho hr hoJ hk h0 h1 hdiff hl
  classical
  have hp := piv_pos hs
  set v := col s (pj s (piv_pos hs)) with hvdef
  have hR : InRing v := col_inRing s _
  have hU : IsUnitVec v := col_unit s _
  -- the first syllable of `s` is `H_[z,P]`
  obtain ⟨i1, P, z1, hz1P, hz1, hz1le, -, -, hPJ, -, hsame, hmin1, hmin2, hsyl⟩ :=
    syl_pos_form hs hk
  have ez1 : z1 = z := Fin.ext (by rw [hz1, hz])
  subst z1
  have ei1 : i1 = z := le_antisymm (hmin1 z h0) hz1le
  subst i1
  have hsyl' : syl s = FreeMonoid.of (Gen.H z P hz1P) := by
    rw [hsyl, dif_neg (lt_irrefl _), mul_one]
  -- the state `r = H_[z,o] s`
  obtain ⟨hlr, hnumr, hrz, hro, hrd, hr0⟩ := hv_odd_diff hR (ne_of_lt hzo) h0 h1 hdiff
  have hidx : ∀ i ∈ (Gen.H z o hzo).idx, (i : ℕ) < piv s := by
    intro i hi; simp [Gen.idx] at hi; rcases hi with rfl | rfl <;> omega
  have hpiv : piv (sem n (Gen.H z o hzo) * s) = piv s := piv_eq_of_col hp hidx (fun h => hk (by
      rw [← hlr, show hv z o v = gv (Gen.H z o hzo) v from rfl, h]
      exact lde_single (Or.inl rfl)))
  have hcolr : col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr)) = hv z o v := by
    have : pj _ (piv_pos hr) = pj s hp := Fin.ext (by simp only [pj]; rw [hpiv])
    rw [this, col_sem_mul]; rfl
  have hkr : lde (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) ≠ 0 := by
    rw [hcolr, hlr]; exact hk
  have hodds : oddSet (hv z o v) = oddSet v := by
    ext i
    rw [mem_oddSet, mem_oddSet]
    by_cases h1' : i = z
    · subst h1'; exact iff_of_true hrz h0
    by_cases h2' : i = o
    · subst h2'; exact iff_of_true hro h1
    rw [hnumr i h1' h2']
  have hlev : lev (sem n (Gen.H z o hzo) * s) = lev s := by
    rw [lev, lev, hpiv, pcol_eq (piv_pos hr), pcol_eq hp, hcolr, kl_eq_of hlr hodds]
  -- the first syllable of `r` is `H_[z,P']`
  obtain ⟨i1', P', z2, hz2P', hz2, hz2le, -, -, hP'J, -, hsame', hmin1', hmin2', hsylr⟩ :=
    syl_pos_form hr hkr
  have ez2 : z2 = z := Fin.ext (by rw [hz2, hz])
  subst z2
  rw [hcolr] at hsame' hmin1' hmin2'
  have ei1' : i1' = z := le_antisymm (hmin1' z hrz) hz2le
  subst i1'
  have hsylr' : syl (sem n (Gen.H z o hzo) * s) = FreeMonoid.of (Gen.H z P' hz2P') := by
    rw [hsylr, dif_neg (lt_irrefl _), mul_one]
  rw [hpiv] at hP'J
  have hP'o : P' ≠ o := by rintro rfl; exact hrd hsame'
  have hP'z : P' ≠ z := ne_of_gt hz2P'
  have hPz : P ≠ z := ne_of_gt hz1P
  have hPo : P ≠ o := by rintro rfl; exact hdiff hsame
  have hvP' : num (hv z o v) P' = num v P' := hnumr P' hP'z hP'o
  have hsame'' : SameOdd (num (hv z o v) z) (num v P') := by rw [← hvP']; exact hsame'
  -- the fourth odd entry `Q`, and `P' ∈ {P, Q}`
  obtain ⟨Q, hQz, hQo, hQP, hsQ, hset⟩ := four_odd hR hU hk h1 hdiff (Ne.symm hPz) hsame hl
  have hP'PQ : P' = P ∨ P' = Q := by
    have hP'odd : P' ∈ oddSet v := by rw [mem_oddSet]; exact hsame''.2.1
    rw [hset] at hP'odd
    simp only [mem_insert, mem_singleton] at hP'odd
    rcases hP'odd with h | h | h | h
    · exact absurd h hP'z
    · exact absurd h hP'o
    · exact Or.inl h
    · exact Or.inr h
  -- indices
  have hzP' := Fin.val_ne_of_ne hPz
  have hoP' := Fin.val_ne_of_ne hPo
  have hzQ' := Fin.val_ne_of_ne hQz
  have hoQ' := Fin.val_ne_of_ne hQo
  have hPQ' := Fin.val_ne_of_ne hQP
  have hQJ : (Q : ℕ) < piv s := pcol_low hp (ne_zero_of_odd hR hsQ.2.1)
  have h4 : 4 ≤ piv s := by omega
  have hoQ : o < Q := Fin.lt_def.2 (by omega)
  have hη : Odd (((num v z).re + (num v o).re) / 2) ↔ Odd (num v P').im := by
    have := hsame''.2.2; rw [hr0] at this; exact this
  -- the square from a join
  have hrun1 : ∀ g : Gen n, run [g] s = sem n g * s := fun g => by rw [run_cons, run_nil]
  have L0 : lev (run [Gen.H z P hz1P] s) < lev s := by
    rw [hrun1]; exact lev_pair_lt hp hz1P hPJ hk hsame
  have L1 : lev (run [Gen.H o Q hoQ, Gen.H z P hz1P] s) < lev s := by
    rw [run_cons, hrun1]
    exact lev_two_pairs hs hk hz1P hoQ hPJ hQJ hsame hsQ (Ne.symm (ne_of_lt hzo)) (Ne.symm hPo)
      hQz hQP
  have L2 : lev (run [Gen.H z P' hz2P', Gen.H z o hzo] s) < lev s := by
    have := lev_syl_lt hr
    rw [hsylr', FreeMonoid.lift_eval_of] at this
    rw [run_cons, hrun1, ← hlev]; exact this
  refine Join.square hs hr (A := [Gen.H z P hz1P]) (B := [Gen.H z P' hz2P', Gen.H z o hzo])
    (by rw [hsyl']; exact Derivable.refl _) (by rw [hsylr']; exact Derivable.refl _) ?_

  -- the partner `Q''` of `1` in `r`
  have hRr : InRing (hv z o v) := by rw [← hcolr]; exact col_inRing _ _
  have hUr : IsUnitVec (hv z o v) := by rw [← hcolr]; exact col_unit _ _
  have hkr' : lde (hv z o v) ≠ 0 := by rw [hlr]; exact hk
  obtain ⟨Q'', hQ''z, hQ''o, hQ''P', hsQ'', hsetr⟩ := four_odd hRr hUr hkr' hro hrd
    (Ne.symm hP'z) hsame' (by rw [hodds]; exact hl)
  have hQ''PQ : (Q'' = Q ∧ P' = P) ∨ (Q'' = P ∧ P' = Q) := by
    have hm : Q'' ∈ oddSet v := by rw [← hodds, hsetr]; simp
    rw [hset] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with h | h | h | h
    · exact absurd h hQ''z
    · exact absurd h hQ''o
    · rcases hP'PQ with h' | h'
      · exact absurd (h.trans h'.symm) hQ''P'
      · exact Or.inr ⟨h, h'⟩
    · rcases hP'PQ with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact absurd (h.trans h'.symm) hQ''P'
  have hQ''J : (Q'' : ℕ) < piv s := by
    rcases hQ''PQ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hQJ
    · exact hPJ
  have hoQ'' : o < Q'' := Fin.lt_def.2 (by
    rcases hQ''PQ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega)
  have L3 : lev (run [Gen.H o Q'' hoQ'', Gen.H z P' hz2P', Gen.H z o hzo] s) < lev s := by
    rw [run_cons, run_cons, hrun1, ← hlev]
    have hpr := piv_pos hr
    have := lev_two_pairs hr hkr hz2P' hoQ'' (by rw [hpiv]; exact hP'J) (by rw [hpiv]; exact hQ''J)
      (by rw [hcolr]; exact hsame') (by rw [hcolr]; exact hsQ'')
      (Ne.symm (ne_of_lt hzo)) (Ne.symm hP'o) hQ''z hQ''P'
    exact this
  refine Join.extend (a := Gen.H o Q hoQ) (b := Gen.H o Q'' hoQ'') ?_ (rl_a3 _) L0 L1 L2
  -- sort `P` to `2` and `Q` to `3`
  obtain ⟨p2, hp2v⟩ : ∃ p : Fin n, (p : ℕ) = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨p3, hp3v⟩ : ∃ p : Fin n, (p : ℕ) = 3 := ⟨⟨3, by omega⟩, rfl⟩
  have hlowA : ∀ g ∈ [Gen.H o Q hoQ, Gen.H z P hz1P], LowH g := by
    intro g hg; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl
    · exact lowH_pair hoQ (by omega)
    · exact lowH_pair hz1P (by omega)
  have hlowB : ∀ g ∈ [Gen.H o Q'' hoQ'', Gen.H z P' hz2P', Gen.H z o hzo], LowH g := by
    intro g hg; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact lowH_pair hoQ'' (by omega)
    · exact lowH_pair hz2P' (by omega)
    · exact lowH_pair hzo (by omega)
  have hle2 : p2 ≤ P := Fin.le_def.2 (by omega)
  have h2p : 2 ≤ (p2 : ℕ) := by omega
  have hzp2 : z ≠ p2 := fun h => by have := congrArg Fin.val h; omega
  have hzp3 : z ≠ p3 := fun h => by have := congrArg Fin.val h; omega
  refine move_opt hs hk (p := p2) (c := P) hle2 h2p hPJ hlowA hlowB L1 L3 (i0 := z)
    ⟨hzp2, hPz.symm⟩ h0 fun s1 hs1 hl1 hpiv1 hnum1 hσ1 hρ1 => ?_
  obtain ⟨Q1, hQ1⟩ : ∃ q, Equiv.swap p2 P Q = q := ⟨_, rfl⟩
  have hQ1c : (Q1 = P ∧ (Q : ℕ) = 2) ∨ (Q1 = Q ∧ (Q : ℕ) ≠ 2) := by
    by_cases ha : Q = p2
    · refine Or.inl ⟨?_, by rw [ha, hp2v]⟩
      rw [← hQ1, ha, Equiv.swap_apply_left]
    · refine Or.inr ⟨?_, fun h => ha (Fin.ext (by rw [h, hp2v]))⟩
      rw [← hQ1, Equiv.swap_apply_of_ne_of_ne ha hQP]
  have hQ1v : 3 ≤ (Q1 : ℕ) := by
    rcases hQ1c with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] <;> omega
  have hQ1J : (Q1 : ℕ) < piv s1 := by
    rcases hQ1c with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hpiv1, h]
    · exact hPJ
    · exact hQJ
  have hzQ1 : z ≠ Q1 := fun h => by have := congrArg Fin.val h; omega
  have hle3 : p3 ≤ Q1 := Fin.le_def.2 (by omega)
  have h3p : 2 ≤ (p3 : ℕ) := by omega
  refine move_opt hs1 (by rw [hl1]; exact hk) (p := p3) (c := Q1) hle3 h3p hQ1J
    (lowH_map hle2 h2p hlowA) (lowH_map hle2 h2p hlowB) hσ1 hρ1 (i0 := z) ⟨hzp3, hzQ1⟩
    (by rw [hnum1, Equiv.swap_apply_of_ne_of_ne hzp2 hPz.symm]; exact h0)
    fun s2 hs2 hl2 hpiv2 hnum2 _ _ => ?_
  -- the state `s₂`
  have h4' : 4 ≤ piv s2 := by rw [hpiv2, hpiv1]; exact h4
  have hk2 : lde (col s2 (pj s2 (piv_pos hs2))) ≠ 0 := by rw [hl2, hl1]; exact hk
  have hnum : ∀ i, num (col s2 (pj s2 (piv_pos hs2))) i =
      num v (((Equiv.swap p3 Q1).trans (Equiv.swap p2 P)) i) := by
    intro i; rw [hnum2, hnum1]; rfl
  have hcl : ∀ j : Fin 4, ((Fin.castLE (h4'.trans (piv_le_n s2)) j : Fin n) : ℕ) = j :=
    fun j => Fin.val_castLE _ _
  have e0 : ((Equiv.swap p3 Q1).trans (Equiv.swap p2 P)) (Fin.castLE (h4'.trans (piv_le_n s2)) 0)
      = z := by
    have hx := hcl 0
    simp only [Fin.val_zero] at hx
    show Equiv.swap p2 P (Equiv.swap p3 Q1 _) = z
    rw [swap_far (p := p3) (c := Q1) (by omega) (by omega),
      swap_far (p := p2) (c := P) (by omega) (by omega)]
    exact Fin.ext (by omega)
  have e1 : ((Equiv.swap p3 Q1).trans (Equiv.swap p2 P)) (Fin.castLE (h4'.trans (piv_le_n s2)) 1)
      = o := by
    have hx := hcl 1
    simp only [Fin.val_one] at hx
    show Equiv.swap p2 P (Equiv.swap p3 Q1 _) = o
    rw [swap_far (p := p3) (c := Q1) (by omega) (by omega),
      swap_far (p := p2) (c := P) (by omega) (by omega)]
    exact Fin.ext (by omega)
  have e2 : ((Equiv.swap p3 Q1).trans (Equiv.swap p2 P)) (Fin.castLE (h4'.trans (piv_le_n s2)) 2)
      = P := by
    have hx := hcl 2
    simp only [Fin.val_two] at hx
    show Equiv.swap p2 P (Equiv.swap p3 Q1 _) = P
    rw [swap_far (p := p3) (c := Q1) (by omega) (by omega),
      show Fin.castLE (h4'.trans (piv_le_n s2)) (2 : Fin 4) = p2 from Fin.ext (by omega)]
    exact Equiv.swap_apply_left p2 P
  have e3 : ((Equiv.swap p3 Q1).trans (Equiv.swap p2 P)) (Fin.castLE (h4'.trans (piv_le_n s2)) 3)
      = Q := by
    have hx : ((Fin.castLE (h4'.trans (piv_le_n s2)) (3 : Fin 4) : Fin n) : ℕ) = 3 := hcl 3
    show Equiv.swap p2 P (Equiv.swap p3 Q1 _) = Q
    rw [show Fin.castLE (h4'.trans (piv_le_n s2)) (3 : Fin 4) = p3 from Fin.ext (by omega),
      Equiv.swap_apply_left, ← hQ1, Equiv.swap_apply_self]
  have hτ : ∀ j : Fin 4, ((Equiv.swap p3 Q1).trans (Equiv.swap p2 P))
      (Fin.castLE (h4'.trans (piv_le_n s2)) j) = ![z, o, P, Q] j := by
    intro j; fin_cases j
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  have hfin := sorted_join hs hs2 hk2 h4' _ hnum hτ hset h0 hdiff h1 hsame hsQ
  -- the words
  have hc0 : z = Fin.castLE (h4'.trans (piv_le_n s2)) (0 : Fin 4) := Fin.ext (by simp [hz])
  have hc1 : o = Fin.castLE (h4'.trans (piv_le_n s2)) (1 : Fin 4) := Fin.ext (by simp [ho])
  have hc2 : p2 = Fin.castLE (h4'.trans (piv_le_n s2)) (2 : Fin 4) := Fin.ext (by simp [hp2v])
  have hc3 : p3 = Fin.castLE (h4'.trans (piv_le_n s2)) (3 : Fin 4) := Fin.ext (by simp [hp3v])
  have hP2 : Equiv.swap p3 Q1 (Equiv.swap p2 P P) = p2 := by
    rw [Equiv.swap_apply_right, swap_far (p := p3) (c := Q1) (i := p2) (by omega) (by omega)]
  have hQ3 : Equiv.swap p3 Q1 (Equiv.swap p2 P Q) = p3 := by
    rw [hQ1, Equiv.swap_apply_right]
  have ho1 : Equiv.swap p3 Q1 (Equiv.swap p2 P o) = o := by
    rw [swap_far (p := p2) (c := P) (i := o) (by omega) (by omega),
      swap_far (p := p3) (c := Q1) (i := o) (by omega) (by omega)]
  have hxo : (o : ℕ) ≤ 1 := by omega
  have hxz : (z : ℕ) ≤ 1 := by omega
  have hwA : (([Gen.H o Q hoQ, Gen.H z P hz1P].map (swapG p2 P)).map (swapG p3 Q1)) =
      ([hL 1 3, hL 0 2] : List (Gen 4)).map (Gen.map (Fin.castLE (h4'.trans (piv_le_n s2)))
        (Fin.strictMono_castLE _)) := by
    simp only [List.map_cons, List.map_nil]
    refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)
    · exact swapG2_H hle2 h2p hle3 h3p hxo hoQ _ hc1 (hQ3.trans hc3)
    · exact swapG2_H hle2 h2p hle3 h3p hxz hz1P _ hc0 (hP2.trans hc2)
  have hd : ¬(Odd (num v z).im ↔ Odd (num v o).im) := fun h => hdiff ⟨h0, h1, h⟩
  rcases hQ''PQ with ⟨hq, hpp⟩ | ⟨hq, hpp⟩
  · have hwB : (([Gen.H o Q'' hoQ'', Gen.H z P' hz2P', Gen.H z o hzo].map (swapG p2 P)).map
        (swapG p3 Q1)) = ([hL 1 3, hL 0 2, hL 0 1] : List (Gen 4)).map
          (Gen.map (Fin.castLE (h4'.trans (piv_le_n s2))) (Fin.strictMono_castLE _)) := by
      simp only [List.map_cons, List.map_nil]
      refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))
      · exact swapG2_H hle2 h2p hle3 h3p hxo hoQ'' _ hc1 (by rw [hq]; exact hQ3.trans hc3)
      · exact swapG2_H hle2 h2p hle3 h3p hxz hz2P' _ hc0 (by rw [hpp]; exact hP2.trans hc2)
      · exact swapG2_H hle2 h2p hle3 h3p hxz hzo _ hc0 (ho1.trans hc1)
    rw [hwA, hwB]
    refine hfin.1 ?_
    show Odd (((num v z).re + (num v o).re) / 2) ↔ Odd (num v z).im
    rw [hpp] at hη
    exact hη.trans hsame.2.2.symm
  · have hwB : (([Gen.H o Q'' hoQ'', Gen.H z P' hz2P', Gen.H z o hzo].map (swapG p2 P)).map
        (swapG p3 Q1)) = ([hL 1 2, hL 0 3, hL 0 1] : List (Gen 4)).map
          (Gen.map (Fin.castLE (h4'.trans (piv_le_n s2))) (Fin.strictMono_castLE _)) := by
      simp only [List.map_cons, List.map_nil]
      refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))
      · exact swapG2_H hle2 h2p hle3 h3p hxo hoQ'' _ hc1 (by rw [hq]; exact hP2.trans hc2)
      · exact swapG2_H hle2 h2p hle3 h3p hxz hz2P' _ hc0 (by rw [hpp]; exact hQ3.trans hc3)
      · exact swapG2_H hle2 h2p hle3 h3p hxz hzo _ hc0 (ho1.trans hc1)
    rw [hwA, hwB]
    refine hfin.2 ?_
    show Odd (((num v z).re + (num v o).re) / 2) ↔ ¬Odd (num v z).im
    rw [hpp] at hη
    rw [hη, ← hsQ.2.2]
    exact ⟨fun h hz' => hd ⟨fun _ => h, fun _ => hz'⟩,
      fun h => by_contra fun h' => hd ⟨fun hz' => absurd hz' h, fun ho' => absurd ho' h'⟩⟩

end QCert.HadamardPi
