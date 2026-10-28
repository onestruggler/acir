/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Four odd entries of one class

On a window of four odd numerators of one class, written
`u_j = (2 a_j + 1) + (2 b_j + c) √2`, a word `w` on the window is *good* for
the parity `par` of `a_0 + a_1 + a_2 + a_3` (`Good4`) when, for every such
pattern, its numerators at the old exponent are integral and one of them is
even.  A good word lowers the level, whatever the entries outside the
window are (`lev_lt_of_good4`): this is the global level comparison of
`Window.lean` along the order embedding of the window.
-/
import QCert.HadamardPi.Window
import QCert.HadamardPi.Check

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-- The numerators of the pattern. -/
def Pat4 (a b : Fin 4 → ℤ) (c : ℤ) : Fin 4 → ℤ√2 := fun j => ⟨2 * a j + 1, 2 * b j + c⟩

/-- The word `w` keeps the numerators integral at the old exponent, with an
even one, for every pattern of parity `par`. -/
def Good4 (par : ℤ) (w : List (Gen 4)) : Prop :=
  ∀ (a b : Fin 4 → ℤ) (c mm : ℤ), a 0 + a 1 + a 2 + a 3 = 2 * mm + par →
    ∃ U' : Fin 4 → ℤ√2, (∀ j, rt2 ^ hcntw w * U' j = scw w (Pat4 a b c) j) ∧
      ∃ j, ¬Odd (U' j).re

@[simp] theorem rt2_re : rt2.re = 0 := rfl

@[simp] theorem rt2_im : rt2.im = 1 := rfl

@[simp] theorem re_rt2_mul (x : ℤ√2) : (rt2 * x).re = 2 * x.im := by simp [rt2]

@[simp] theorem im_rt2_mul (x : ℤ√2) : (rt2 * x).im = x.re := by simp [rt2]

@[simp] theorem Pat4_re (a b : Fin 4 → ℤ) (c : ℤ) (j : Fin 4) : (Pat4 a b c j).re = 2 * a j + 1 :=
  rfl

@[simp] theorem Pat4_im (a b : Fin 4 → ℤ) (c : ℤ) (j : Fin 4) : (Pat4 a b c j).im = 2 * b j + c :=
  rfl

theorem cancel_sqrt2_pow {h K : ℕ} {X Y : ℝ}
    (e : Real.sqrt 2 ^ h * X = Real.sqrt 2 ^ (K + h) * Y) : X = Real.sqrt 2 ^ K * Y := by
  have h0 : Real.sqrt 2 ^ h ≠ 0 := pow_ne_zero _ sqrt2_ne_zero
  apply mul_left_cancel₀ h0
  rw [e, pow_add]; ring

theorem run_eq_lift (w : List (Gen n)) (s : O n) :
    run w s = FreeMonoid.lift (sem n) (ofList w) * s := rfl

/-- A good word on a window of four odd entries of one class lowers the
level. -/
theorem lev_lt_of_good4 {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (f : Fin 4 → Fin n) (hf : StrictMono f) (hfJ : ∀ j, (f j : ℕ) < piv s)
    {a b : Fin 4 → ℤ} {c mm par : ℤ}
    (hpat : ∀ j, num (col s (pj s (piv_pos hs))) (f j) = Pat4 a b c j)
    (hsum : a 0 + a 1 + a 2 + a 3 = 2 * mm + par)
    {w : List (Gen 4)} (hw : Good4 par w) :
    lev (run (w.map (Gen.map f hf)) s) < lev s := by
  classical
  obtain ⟨U', hU', j0, hj0⟩ := hw a b c mm hsum
  set v := col s (pj s (piv_pos hs)) with hv
  have hR : InRing v := col_inRing s _
  set w' := w.map (Gen.map f hf) with hw'
  have hcol : col (run w' s) (pj s (piv_pos hs)) = wv (ofList w') v := by
    rw [run_eq_lift]; exact col_lift_mul' _ _ _
  have hsc := toReal_scw w' (U := num v) (x := v) (K := lde v) (toReal_num hR)
  have hfun : (num v ∘ f) = Pat4 a b c := funext hpat
  -- the letters of `w'` act on the window
  have hidx : ∀ g ∈ w', ∀ i ∈ g.idx, ∃ j, f j = i := by
    intro g hg i hi
    rw [hw', List.mem_map] at hg
    obtain ⟨g0, -, rfl⟩ := hg
    exact idx_map f hf g0 hi
  let u' : Fin n → ℤ√2 := fun i => if h : ∃ j, f j = i then U' h.choose else num v i
  have hu'f : ∀ j, u' (f j) = U' j := by
    intro j
    have h : ∃ j', f j' = f j := ⟨j, rfl⟩
    simp only [u', dif_pos h]
    rw [hf.injective h.choose_spec]
  have hpiv : piv (run w' s) ≤ piv s := by
    rw [run_eq_lift]
    apply piv_le_of_below
    intro g hg i hi
    obtain ⟨j, rfl⟩ := hidx g (by simpa using hg) i hi
    exact hfJ j
  refine lev_lt_of_window hs hk hpiv (univ.map ⟨f, hf.injective⟩) (u' := u') ?_ ?_ ?_
  · intro i
    rw [hcol]
    by_cases h : ∃ j, f j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hu'f]
      have e := hsc (f j)
      rw [scw_map, hcntw_map, hfun, ← hU' j, map_mul, map_pow, toReal_rt2] at e
      exact cancel_sqrt2_pow e
    · have hu : u' i = num v i := by simp only [u', dif_neg h]
      rw [hu]
      have e := hsc i
      rw [scw_out w' (num v) i (fun g hg hi => h (hidx g hg i hi)), map_mul, map_pow,
        toReal_rt2] at e
      exact cancel_sqrt2_pow e
  · intro i hi
    have h : ¬∃ j, f j = i := by
      rintro ⟨j, rfl⟩; exact hi (mem_map_of_mem _ (mem_univ j))
    simp only [u', dif_neg h]
    rfl
  · apply card_lt_card
    refine ⟨fun i hi => ?_, fun hsub => ?_⟩
    · rw [mem_filter, Finset.mem_map] at hi ⊢
      obtain ⟨⟨j, -, rfl⟩, -⟩ := hi
      exact ⟨⟨j, mem_univ j, rfl⟩, by show Odd (num v (f j)).re; rw [hpat]; exact ⟨a j, rfl⟩⟩
    · have hm : f j0 ∈ (univ.map ⟨f, hf.injective⟩).filter fun i => Odd (num v i).re := by
        rw [mem_filter, Finset.mem_map]
        exact ⟨⟨j0, mem_univ j0, rfl⟩, by show Odd (num v (f j0)).re; rw [hpat]; exact ⟨a j0, rfl⟩⟩
      have := (mem_filter.1 (hsub hm)).2
      rw [hu'f] at this
      exact hj0 this

/-! ### Windows of any size -/

/-- A word on a window, with explicit numerators `U'` at the old exponent and
fewer odd ones than the window had, lowers the level. -/
theorem lev_lt_of_window_word {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) {w : ℕ}
    (f : Fin w → Fin n) (hf : StrictMono f) (hfJ : ∀ j, (f j : ℕ) < piv s)
    {word : List (Gen w)} (U' : Fin w → ℤ√2)
    (hU' : ∀ j, rt2 ^ hcntw word * U' j = scw word (fun j => num (col s (pj s (piv_pos hs))) (f j)) j)
    (hcount : (univ.filter fun j => Odd (U' j).re).card <
      (univ.filter fun j => Odd (num (col s (pj s (piv_pos hs))) (f j)).re).card) :
    lev (run (word.map (Gen.map f hf)) s) < lev s := by
  classical
  set v := col s (pj s (piv_pos hs)) with hv
  have hR : InRing v := col_inRing s _
  set w' := word.map (Gen.map f hf) with hw'
  have hcol : col (run w' s) (pj s (piv_pos hs)) = wv (ofList w') v := by
    rw [run_eq_lift]; exact col_lift_mul' _ _ _
  have hsc := toReal_scw w' (U := num v) (x := v) (K := lde v) (toReal_num hR)
  have hidx : ∀ g ∈ w', ∀ i ∈ g.idx, ∃ j, f j = i := by
    intro g hg i hi
    rw [hw', List.mem_map] at hg
    obtain ⟨g0, -, rfl⟩ := hg
    exact idx_map f hf g0 hi
  let u' : Fin n → ℤ√2 := fun i => if h : ∃ j, f j = i then U' h.choose else num v i
  have hu'f : ∀ j, u' (f j) = U' j := by
    intro j
    have h : ∃ j', f j' = f j := ⟨j, rfl⟩
    simp only [u', dif_pos h]
    rw [hf.injective h.choose_spec]
  have hpiv : piv (run w' s) ≤ piv s := by
    rw [run_eq_lift]
    apply piv_le_of_below
    intro g hg i hi
    obtain ⟨j, rfl⟩ := hidx g (by simpa using hg) i hi
    exact hfJ j
  refine lev_lt_of_window hs hk hpiv (univ.map ⟨f, hf.injective⟩) (u' := u') ?_ ?_ ?_
  · intro i
    rw [hcol]
    by_cases h : ∃ j, f j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hu'f]
      have e := hsc (f j)
      have hU'' : rt2 ^ hcntw word * U' j = scw word (num v ∘ f) j := hU' j
      rw [scw_map, hcntw_map, ← hU'', map_mul, map_pow, toReal_rt2] at e
      exact cancel_sqrt2_pow e
    · have hu : u' i = num v i := by simp only [u', dif_neg h]
      rw [hu]
      have e := hsc i
      rw [scw_out w' (num v) i (fun g hg hi => h (hidx g hg i hi)), map_mul, map_pow,
        toReal_rt2] at e
      exact cancel_sqrt2_pow e
  · intro i hi
    have h : ¬∃ j, f j = i := by
      rintro ⟨j, rfl⟩; exact hi (mem_map_of_mem _ (mem_univ j))
    simp only [u', dif_neg h]
    rfl
  · have e1 : ((univ.map ⟨f, hf.injective⟩).filter fun i => Odd (u' i).re) =
        (univ.filter fun j => Odd (U' j).re).map ⟨f, hf.injective⟩ := by
      ext i
      simp only [mem_filter, Finset.mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨j, rfl⟩, h⟩; exact ⟨j, by rwa [hu'f] at h, rfl⟩
      · rintro ⟨j, h, rfl⟩; exact ⟨⟨j, rfl⟩, by rwa [hu'f]⟩
    have e2 : ((univ.map ⟨f, hf.injective⟩).filter fun i => Odd (num v i).re) =
        (univ.filter fun j => Odd (num v (f j)).re).map ⟨f, hf.injective⟩ := by
      ext i
      simp only [mem_filter, Finset.mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨j, rfl⟩, h⟩; exact ⟨j, h, rfl⟩
      · rintro ⟨j, h, rfl⟩; exact ⟨⟨j, rfl⟩, h⟩
    rw [e1, e2, card_map, card_map]
    exact hcount

/-- Counting odd entries of a window: at most those of `S` on one side, at
least those of `T` on the other. -/
theorem card_filter_lt {w : ℕ} {P P' : Fin w → Prop} [DecidablePred P] [DecidablePred P']
    (S T : Finset (Fin w)) (hS : ∀ j, j ∉ S → ¬P' j) (hT : ∀ j ∈ T, P j) (hST : S.card < T.card) :
    (univ.filter P').card < (univ.filter P).card := by
  have h1 : (univ.filter P') ⊆ S := fun j hj => by
    by_contra h; exact hS j h (mem_filter.1 hj).2
  have h2 : T ⊆ univ.filter P := fun j hj => mem_filter.2 ⟨mem_univ _, hT j hj⟩
  exact lt_of_le_of_lt (card_le_card h1) (lt_of_lt_of_le hST (card_le_card h2))

/-- Every state of a path given by its suffixes. -/
theorem pathLt_of_drop {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} :
    ∀ (w : List (Gen n)) (t : O n), (∀ k ≤ w.length, lev (run (w.drop k) t) < L) → PathLt L w t
  | [], t, h => by simpa using h 0 (le_refl _)
  | g :: w, t, h => ⟨pathLt_of_drop w t fun k hk => by
      simpa using h (k + 1) (by simp; omega), by simpa using h 0 (Nat.zero_le _)⟩

end QCert.HadamardPi
