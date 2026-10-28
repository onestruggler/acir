/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Steps of the case analysis on patterns

The case analysis of `CaseFour.lean` is a tree whose nodes are states `s`
with a window `0, …, w-1` of the pivot column described by a pattern, and
the goal of a join `Join s A B` for two fixed words `A`, `B` on the indices
`0, …, 3`.  The steps:

* `leaf_join`: a checked path with a derivation (`join_of_check`) along the
  embedding `Fin.castLE` of the window;
* `transfer_mono`: a transfer along a monomial word on the window
  (`Join.transfer`), the new window being computed (`pat_after`);
* `extend_entry`: an entry outside the window, of depth `δ`, moved next to
  the window by a transposition, which extends the window by one entry with
  two new parameters (`dent`);
* `tail_odd_entry`: an entry outside the window forced by an odd number of
  odd entries in the window (Clément's Lemma 2.1, without classes), and
  `tail_class_even`: an even class count in the window gives an even count
  outside.
-/
import QCert.HadamardPi.SymSplit

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### The embedding of the window -/

theorem map_castLE_castLE {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) (l : List (Gen a)) :
    (l.map (Gen.map (Fin.castLE h1) (Fin.strictMono_castLE h1))).map
        (Gen.map (Fin.castLE h2) (Fin.strictMono_castLE h2)) =
      l.map (Gen.map (Fin.castLE (h1.trans h2)) (Fin.strictMono_castLE (h1.trans h2))) := by
  rw [List.map_map]
  congr 1
  funext g
  cases g <;> rfl

theorem castLE_lt {s : O n} {w : ℕ} (hw : w ≤ piv s) (j : Fin w) :
    ((Fin.castLE (hw.trans (piv_le_n s)) j : Fin n) : ℕ) < piv s := by
  simp only [Fin.coe_castLE]; omega

/-- A leaf: a derivation and a checked path on the window. -/
theorem leaf_join {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
      zev (P.getD j dZ) t)
    {D A B : List (Gen w)} (hd : Derivable Fig6 (ofList (D ++ A)) (ofList B))
    (hc : pathOK P D A = true) :
    Join s (A.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
      (B.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) :=
  join_of_check _ (Fin.strictMono_castLE (hw.trans (piv_le_n s))) hs hk (castLE_lt hw) hP hd hc

/-- The state `A s` of a checked word is below `s`. -/
theorem lev_lt_of_check {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
      zev (P.getD j dZ) t)
    {A : List (Gen w)} (hc : pathOK P [] A = true) :
    lev (run (A.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
      (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) s) < lev s := by
  have := path_of_check _ (Fin.strictMono_castLE (hw.trans (piv_le_n s))) hs hk (castLE_lt hw) hP
    (D := []) hc
  simpa [PathLt] using this

/-! ### Monomial transfers -/

/-- All letters monomial. -/
def allMono {w : ℕ} : List (Gen w) → Bool
  | [] => true
  | .H _ _ _ :: _ => false
  | _ :: l => allMono l

theorem mono_of_allMono {w : ℕ} : ∀ {l : List (Gen w)}, allMono l = true → ∀ g ∈ l, IsMono g
  | [], _, g, hg => by simp at hg
  | .H _ _ _ :: _, h, _, _ => by simp [allMono] at h
  | .Z a :: l, h, g, hg => by
    rcases List.mem_cons.1 hg with rfl | hg
    · trivial
    · exact mono_of_allMono (l := l) (by simpa [allMono] using h) g hg
  | .X a b hab :: l, h, g, hg => by
    rcases List.mem_cons.1 hg with rfl | hg
    · trivial
    · exact mono_of_allMono (l := l) (by simpa [allMono] using h) g hg

theorem allMono_map {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {l : List (Gen w)}
    (h : allMono l = true) : ∀ g ∈ l.map (Gen.map f hf), IsMono g := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := mono_of_allMono h g0 hg0
  cases g0 <;> simp_all [Gen.map, IsMono]

theorem idx_lt_of_window {w : ℕ} {s : O n} (hw : w ≤ piv s) (l : List (Gen w)) :
    ∀ g ∈ l.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s)))), ∀ i ∈ g.idx, (i : ℕ) < piv s := by
  intro g hg i hi
  rw [List.mem_map] at hg
  obtain ⟨g0, -, rfl⟩ := hg
  obtain ⟨j, rfl⟩ := idx_map _ _ g0 hi
  exact castLE_lt hw j

/-- A transfer along a monomial word `m` on the window, with
`A' m ≈ μ A` and `B' m ≈ ν B`: a join at `m s`, whose window has the
pattern `divAll P m`, gives one at `s`. -/
theorem transfer_mono {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
      zev (P.getD j dZ) t)
    {T : ℤ√2 → Prop}
    (htail : ∀ i : Fin n, w ≤ (i : ℕ) → T (num (col s (pj s (piv_pos hs))) i))
    {m μ ν A A' B B' : List (Gen w)} (hm : allMono m = true) (hμ : allMono μ = true)
    (hν : allMono ν = true)
    (hA : Derivable Fig6 (ofList (A' ++ m)) (ofList (μ ++ A)))
    (hB : Derivable Fig6 (ofList (B' ++ m)) (ofList (ν ++ B)))
    (hc : allSome P m = true) (j0 : Fin w) (ho : oddSure ((divAll P m).getD j0 dZ) = true)
    (hcA : pathOK P [] A = true)
    (hJ : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w ≤ piv s',
      (∀ j : Fin w, num (col s' (pj s' (piv_pos hs'))) (Fin.castLE (hw'.trans (piv_le_n s')) j) =
        zev ((divAll P m).getD j dZ) t) →
      (∀ i : Fin n, w ≤ (i : ℕ) → T (num (col s' (pj s' (piv_pos hs'))) i)) →
      Join s' (A'.map (Gen.map (Fin.castLE (hw'.trans (piv_le_n s')))
          (Fin.strictMono_castLE (hw'.trans (piv_le_n s')))))
        (B'.map (Gen.map (Fin.castLE (hw'.trans (piv_le_n s')))
          (Fin.strictMono_castLE (hw'.trans (piv_le_n s')))))) :
    Join s (A.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
      (B.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) := by
  set f := Fin.castLE (hw.trans (piv_le_n s))
  have hf : StrictMono f := Fin.strictMono_castLE _
  obtain ⟨hs', hpiv, hl, hwin, htl⟩ := pat_after f hf hs hk (castLE_lt hw) hP m hc j0 ho
  have hw' : w ≤ piv (run (m.map (Gen.map f hf)) s) := by rw [hpiv]; exact hw
  have hJ' := hJ _ hs' (by rw [hl]; exact hk) hw' hwin (fun i hi => by
    rw [htl i (fun j hj => by
      have := j.2; rw [← hj] at hi; simp [f] at hi; omega)]
    exact htail i hi)
  have hidx := idx_lt_of_window hw
  have lev0lt : ∀ l : List (Gen w), ∀ g ∈ l.map (Gen.map f hf), ∀ i ∈ g.idx, lev0 i < lev s :=
    fun l g hg i hi => lev0_lt_of_lde (piv_pos hs) (hidx l g hg i hi) hk
  refine Join.transfer (m := m.map (Gen.map f hf)) (μ := μ.map (Gen.map f hf))
    (ν := ν.map (Gen.map f hf)) (A' := A'.map (Gen.map f hf)) (B' := B'.map (Gen.map f hf))
    (fun g hg => ⟨allMono_map f hf hm g hg, fun i hi => le_of_lt (lev0lt m g hg i hi)⟩)
    (fun g hg => ⟨allMono_map f hf hμ g hg, lev0lt μ g hg⟩)
    (fun g hg => ⟨allMono_map f hf hν g hg, lev0lt ν g hg⟩) ?_ ?_
    (lev_lt_of_check hs hk hw hP hcA) hJ'
  · have := der_map f hf hA; simpa only [List.map_append] using this
  · have := der_map f hf hB; simpa only [List.map_append] using this

/-! ### Parity of a sum -/

theorem card_odd_zmod {ι : Type*} [Fintype ι] (x : ι → ℤ) :
    ((univ.filter fun i => Odd (x i)).card : ZMod 2) = ∑ i, (x i : ZMod 2) := by
  classical
  simp only [intCast_zmod2]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem odd_card_of_odd_sum {ι : Type*} [Fintype ι] (x : ι → ℤ) (h : Odd (∑ i, x i)) :
    Odd (univ.filter fun i => Odd (x i)).card := by
  classical
  have key := card_odd_zmod x
  have h1 : ((∑ i, x i : ℤ) : ZMod 2) = 1 := by rw [intCast_zmod2, if_pos h]
  push_cast at h1
  rw [h1] at key
  rw [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even, key]
  decide

/-! ### Extending the window by an entry outside it -/

/-- Letters away from `p`, `q` commute with `X_[p,q]`. -/
theorem comm_far {p q : Fin n} (hpq : p < q) :
    ∀ A : List (Gen n), (∀ g ∈ A, ∀ i ∈ g.idx, i ≠ p ∧ i ≠ q) →
      Derivable Fig6 (ofList (A ++ [Gen.X p q hpq])) (ofList ([Gen.X p q hpq] ++ A))
  | [], _ => Derivable.refl _
  | g :: A, h => by
    have ih := comm_far hpq A (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    have hg := h g List.mem_cons_self
    have step : Derivable Fig6 (ofList [g, Gen.X p q hpq]) (ofList [Gen.X p q hpq, g]) := by
      cases g with
      | Z a =>
        have h1 := hg a (by simp [Gen.idx])
        exact rl_b2 hpq h1.1 h1.2
      | X a b hab =>
        have h1 := hg a (by simp [Gen.idx])
        have h2 := hg b (by simp [Gen.idx])
        exact rl_b3 hab hpq h1.1 h1.2 h2.1 h2.2
      | H c d hcd =>
        have h1 := hg c (by simp [Gen.idx])
        have h2 := hg d (by simp [Gen.idx])
        exact (rl_b5 hpq hcd (Ne.symm h1.1) (Ne.symm h2.1) (Ne.symm h1.2) (Ne.symm h2.2)).symm
    have e1 := der_mid [g] (A ++ [Gen.X p q hpq]) [] ([Gen.X p q hpq] ++ A) ih
    have e2 := der_mid [] [g, Gen.X p q hpq] A [Gen.X p q hpq, g] step
    simp only [List.append_nil, List.nil_append, List.cons_append, List.singleton_append] at e1 e2 ⊢
    exact e1.trans e2

/-- The base of a new entry: `(1 + 2 tₙᵥ) + (γ + 2 tₙᵥ₊₁) √2`. -/
def dbase (γ : Bool) (nv : ℕ) : ZL :=
  (1 :: (List.replicate nv 0 ++ [2, 0]), (if γ then 1 else 0) :: (List.replicate nv 0 ++ [0, 2]))

/-- A new entry of depth `δ` and class `γ`, in the parameters `nv`, `nv + 1`. -/
def dent (δ : ℕ) (γ : Bool) (nv : ℕ) : ZL := zrt2^[δ] (dbase γ nv)

theorem evv_replicate_append : ∀ (k : ℕ) (l : List ℤ) (t : ℕ → ℤ),
    evv (List.replicate k 0 ++ l) t = evv l (fun i => t (i + k))
  | 0, l, t => rfl
  | k + 1, l, t => by
    rw [List.replicate_succ, List.cons_append, evv_cons, evv_replicate_append k l, zero_mul, zero_add]
    rfl

theorem zev_dbase (γ : Bool) (nv : ℕ) (t : ℕ → ℤ) :
    zev (dbase γ nv) t = ⟨1 + 2 * t nv, (if γ then 1 else 0) + 2 * t (nv + 1)⟩ := by
  simp only [dbase, zev]
  rw [evv_c1, evv_c1, evv_replicate_append, evv_replicate_append]
  congr 1 <;> simp only [evv_cons, evv_nil, Nat.zero_add, Nat.add_comm 1 nv] <;> ring

theorem zev_dent (δ : ℕ) (γ : Bool) (nv : ℕ) (t : ℕ → ℤ) :
    zev (dent δ γ nv) t = rt2 ^ δ * ⟨1 + 2 * t nv, (if γ then 1 else 0) + 2 * t (nv + 1)⟩ := by
  rw [dent]
  induction δ with
  | zero => simp [zev_dbase]
  | succ d ih => rw [Function.iterate_succ_apply', zev_zrt2, ih, pow_succ]; ring

/-- The parameters with two more values. -/
def text (t : ℕ → ℤ) (nv : ℕ) (a b : ℤ) : ℕ → ℤ :=
  fun i => if i = nv then a else if i = nv + 1 then b else t i

theorem odd_ne_zero {y : ℤ√2} (h : Odd y.re) : y ≠ 0 := by
  rintro rfl; simp at h

theorem rt2_pow_mul_cancel {δ : ℕ} {y y' : ℤ√2} (h : rt2 ^ δ * y = rt2 ^ δ * y') : y = y' := by
  apply toReal_injective
  have := congrArg toReal h
  rw [map_mul, map_mul, map_pow, toReal_rt2] at this
  exact mul_left_cancel₀ (pow_ne_zero _ sqrt2_ne_zero) this

theorem rt2_pow_mul_ne_zero {δ : ℕ} {y : ℤ√2} (h : y ≠ 0) : rt2 ^ δ * y ≠ 0 := fun h0 =>
  h (rt2_pow_mul_cancel (h0.trans (mul_zero _).symm))

theorem idx_lt_piv_of_num {s : O n} (hs : s ≠ 1) {i : Fin n}
    (h : num (col s (pj s (piv_pos hs))) i ≠ 0) : (i : ℕ) < piv s := by
  apply pcol_low (piv_pos hs)
  intro h0
  apply h
  apply toReal_injective
  rw [toReal_num (col_inRing s _), h0, mul_zero, map_zero]

/-- Extend the window `0, …, w-1` by an entry `i ≥ w` of depth `δ` and class
`γ`, moved to `w` by a transposition. -/
theorem extend_entry {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {nv : ℕ} (hPw : Pwidth P nv = true) (hPl : P.length = w)
    {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
      zev (P.getD j dZ) t)
    (j0 : Fin w) (hj0 : oddSure (P.getD j0 dZ) = true)
    {T : ℤ√2 → Prop} (hT : ∀ u, T u → ¬Odd u.re)
    (htail : ∀ i : Fin n, w ≤ (i : ℕ) → T (num (col s (pj s (piv_pos hs))) i))
    {A B : List (Gen n)} (hA : ∀ g ∈ A, ∀ i ∈ g.idx, (i : ℕ) < w)
    (hB : ∀ g ∈ B, ∀ i ∈ g.idx, (i : ℕ) < w)
    (hσ : lev (run A s) < lev s) (hρ : lev (run B s) < lev s)
    {i : Fin n} (hi : w ≤ (i : ℕ)) {δ : ℕ} {γ : Bool} {y : ℤ√2}
    (hy : rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i) (hyo : Odd y.re)
    (hyc : Odd y.im ↔ γ = true)
    (hJ : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w + 1 ≤ piv s',
      (∀ j : Fin (w + 1),
        num (col s' (pj s' (piv_pos hs'))) (Fin.castLE (hw'.trans (piv_le_n s')) j) =
          zev ((P ++ [dent δ γ nv]).getD j dZ)
            (text t nv ((y.re - 1) / 2) ((y.im - (if γ then 1 else 0)) / 2))) →
      (∀ i : Fin n, w + 1 ≤ (i : ℕ) → T (num (col s' (pj s' (piv_pos hs'))) i)) →
      lev s' = lev s → Join s' A B) :
    Join s A B := by
  classical
  set v := col s (pj s (piv_pos hs)) with hv
  set t' := text t nv ((y.re - 1) / 2) ((y.im - (if γ then 1 else 0)) / 2) with ht'
  have hiJ : (i : ℕ) < piv s := idx_lt_piv_of_num hs (by
    rw [← hy]; exact rt2_pow_mul_ne_zero (odd_ne_zero hyo))
  have hw1 : w + 1 ≤ piv s := by omega
  -- the new entry in the pattern
  have hdent : zev (dent δ γ nv) t' = num v i := by
    have h1 : t' nv = (y.re - 1) / 2 := by simp [ht', text]
    have h2 : t' (nv + 1) = (y.im - (if γ then 1 else 0)) / 2 := by simp [ht', text]
    have hy' : (⟨1 + 2 * ((y.re - 1) / 2),
        (if γ then 1 else 0) + 2 * ((y.im - (if γ then 1 else 0)) / 2)⟩ : ℤ√2) = y := by
      obtain ⟨r, hr⟩ := hyo
      apply Zsqrtd.ext
      · show 1 + 2 * ((y.re - 1) / 2) = y.re; omega
      · show (if γ then 1 else 0) + 2 * ((y.im - (if γ then 1 else 0)) / 2) = y.im
        cases γ
        · simp only [Bool.false_eq_true, if_false, iff_false, Int.not_odd_iff_even] at hyc ⊢
          obtain ⟨m, hm⟩ := hyc; omega
        · simp only [if_true, iff_true] at hyc ⊢
          obtain ⟨m, hm⟩ := hyc; omega
    rw [zev_dent, h1, h2, hy', hy]
  have hPold : ∀ j : ℕ, j < w → zev ((P ++ [dent δ γ nv]).getD j dZ) t' = zev (P.getD j dZ) t := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hPl]; exact hj),
      ← List.getD_eq_getElem?_getD]
    exact zev_congr hPw (fun i hi => by simp [ht', text]; omega) j
  have hPnew : (P ++ [dent δ γ nv]).getD w dZ = dent δ γ nv := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hPl]), hPl, Nat.sub_self]
    rfl
  by_cases hiw : (i : ℕ) = w
  · -- the entry is already at `w`
    refine hJ s hs hk hw1 (fun j => ?_) (fun i' hi' => htail i' (by omega)) rfl
    by_cases hj : (j : ℕ) < w
    · rw [hPold j hj, ← hP ⟨j, hj⟩]; rfl
    · have hjw : (j : ℕ) = w := by have := j.2; omega
      have : Fin.castLE (hw1.trans (piv_le_n s)) j = i := Fin.ext (by simp [hjw, hiw])
      rw [this, show (j : ℕ) = w from hjw, hPnew, hdent]
  · -- move it to `w`
    have hwi : w < (i : ℕ) := by omega
    set pw : Fin n := ⟨w, by omega⟩
    have hpwi : pw < i := Fin.lt_def.2 hwi
    set K := [Gen.X pw i hpwi]
    have hKi : ∀ g ∈ K, ∀ i' ∈ g.idx, (i' : ℕ) < piv s := by
      intro g hg i' hi'
      simp only [K, List.mem_singleton] at hg; subst hg
      simp only [Gen.idx, mem_insert, mem_singleton] at hi'
      rcases hi' with rfl | rfl
      · show w < piv s; omega
      · exact hiJ
    have hsw : ∀ i', scw K (num v) i' = num v (Equiv.swap pw i i') := by
      intro i'
      simp only [K, scw, scg, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    -- an odd entry of the window stays
    have hodd0 : Odd (num v (Equiv.swap pw i (Fin.castLE (hw.trans (piv_le_n s)) j0))).re := by
      have hne1 : Fin.castLE (hw.trans (piv_le_n s)) j0 ≠ pw := by
        intro h; have := congrArg Fin.val h; simp [pw] at this; omega
      have hne2 : Fin.castLE (hw.trans (piv_le_n s)) j0 ≠ i := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, hP]; exact odd_of_oddSure hj0 t
    obtain ⟨hs', hpiv, hl, hnum⟩ := state_after hs hk hKi
      (U := fun i' => num v (Equiv.swap pw i i')) (by
        intro i'; beta_reduce; rw [← hsw i']
        simp only [hcntw, hcnt, K, pow_zero, one_mul, add_zero]; rfl)
      hodd0
    have hlev : lev (run K s) = lev s := by
      refine lev_eq_of_num hs hs' hpiv hl fun i' => ?_
      rw [hnum]
      by_cases h1 : i' = pw
      · subst h1
        rw [Equiv.swap_apply_left]
        exact iff_of_false (fun h => hT _ (htail i hi) h) (fun h => hT _ (htail pw le_rfl) h)
      by_cases h2 : i' = i
      · subst h2
        rw [Equiv.swap_apply_right]
        exact iff_of_false (fun h => hT _ (htail pw le_rfl) h) (fun h => hT _ (htail i' hi) h)
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    refine Join.transfer_gen (K := K) hlev.le ?_ ?_ ?_ ?_ ?_
    · refine comm_far hpwi A fun g hg i' hi' => ⟨?_, ?_⟩ <;> intro h <;> subst h
      · have := hA g hg _ hi'; simp [pw] at this
      · have := hA g hg _ hi'; omega
    · refine comm_far hpwi B fun g hg i' hi' => ⟨?_, ?_⟩ <;> intro h <;> subst h
      · have := hB g hg _ hi'; simp [pw] at this
      · have := hB g hg _ hi'; omega
    · exact mono_path K _ (fun g hg => by
        simp only [K, List.mem_singleton] at hg; subst hg
        exact ⟨trivial, fun i' hi' => lev0_lt_of_lde (piv_pos hs) (hKi _ (by simp [K]) i' hi') hk⟩) hσ
    · exact mono_path K _ (fun g hg => by
        simp only [K, List.mem_singleton] at hg; subst hg
        exact ⟨trivial, fun i' hi' => lev0_lt_of_lde (piv_pos hs) (hKi _ (by simp [K]) i' hi') hk⟩) hρ
    · have hw1' : w + 1 ≤ piv (run K s) := by rw [hpiv]; exact hw1
      refine hJ _ hs' (by rw [hl]; exact hk) hw1' (fun j => ?_) (fun i' hi' => ?_) hlev
      · rw [hnum]
        by_cases hj : (j : ℕ) < w
        · have hne1 : Fin.castLE (hw1'.trans (piv_le_n _)) j ≠ pw := by
            intro h; have := congrArg Fin.val h; simp [pw] at this; omega
          have hne2 : Fin.castLE (hw1'.trans (piv_le_n _)) j ≠ i := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, hPold j hj, ← hP ⟨j, hj⟩]; rfl
        · have hjw : (j : ℕ) = w := by have := j.2; omega
          have : Fin.castLE (hw1'.trans (piv_le_n _)) j = pw := Fin.ext (by simp [pw, hjw])
          rw [this, Equiv.swap_apply_left, show (j : ℕ) = w from hjw, hPnew, hdent]
      · rw [hnum]
        by_cases h2 : i' = i
        · subst h2; rw [Equiv.swap_apply_right]; exact htail pw le_rfl
        · have h1 : i' ≠ pw := by intro h; subst h; simp [pw] at hi'
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact htail i' (by omega)

/-- An entry outside the window forced by an odd number of odd entries in
it: the sum of the rational parts of the window is odd. -/
def sumRe {w : ℕ} (V : List ZL) : List ℤ :=
  (List.range w).foldr (fun j acc => ladd (V.getD j dZ).1 acc) []

theorem evv_foldr_ladd (g : ℕ → List ℤ) (t : ℕ → ℤ) :
    ∀ L : List ℕ, evv (L.foldr (fun j acc => ladd (g j) acc) []) t = (L.map fun j => evv (g j) t).sum
  | [] => rfl
  | j :: L => by simp [evv_ladd, evv_foldr_ladd g t L]

theorem list_sum_range (f : ℕ → ℤ) : ∀ w : ℕ, ((List.range w).map f).sum = ∑ i ∈ Finset.range w, f i
  | 0 => rfl
  | w + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f w,
      Finset.sum_range_succ]; simp

theorem tail_odd_entry {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    (D : List (Gen w)) (δ : ℕ) (hδ : δ + 1 ≤ lde (col s (pj s (piv_pos hs))))
    (hc : allSomeD P D δ = true)
    (htail : ∀ i, (∀ j, f j ≠ i) → ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i)
    (hsum : oddSureL (sumRe (w := w) (divAllD P D δ)) = true) :
    ∃ i, (∀ j, f j ≠ i) ∧ ∃ y, Odd y.re ∧ rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i := by
  classical
  obtain ⟨U, hU, hUf, hUt⟩ := tail_numerators f hf hs hP D δ (by omega) hc htail
  set K := lde (col s (pj s (piv_pos hs))) - δ
  have hu : IsUnitVec (col (run (D.map (Gen.map f hf)) s) (pj s (piv_pos hs))) := col_unit _ _
  have hev := even_card_odd_re U (k := K) (by omega) (sum_sq_at hu hU)
  set W := univ.map (⟨f, hf.injective⟩ : Fin w ↪ Fin n)
  have hsplit := card_filter_split W fun i => Odd (U i).re
  -- the window has an odd number of odd entries
  have hwin : Odd (W.filter fun i => Odd (U i).re).card := by
    rw [Finset.filter_map, Finset.card_map]
    have := odd_of_oddSureL hsum t
    rw [sumRe, evv_foldr_ladd, list_sum_range, ← Fin.sum_univ_eq_sum_range] at this
    have h2 : (∑ i : Fin w, evv ((divAllD P D δ).getD (↑i) dZ).1 (c1 t)) =
        ∑ i : Fin w, (U (f i)).re := by
      refine Finset.sum_congr rfl fun i _ => ?_; rw [hUf]; rfl
    rw [h2] at this
    exact odd_card_of_odd_sum (fun i => (U (f i)).re) this
  have hrest : ((univ \ W).filter fun i => Odd (U i).re).Nonempty := by
    rw [← card_pos]
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0, add_zero] at hsplit
    rw [hsplit] at hev
    exact (Nat.not_even_iff_odd.2 hwin) hev
  obtain ⟨i, hi⟩ := hrest
  rw [mem_filter, mem_sdiff] at hi
  obtain ⟨⟨-, hiW⟩, ho⟩ := hi
  have hiW' : ∀ j, f j ≠ i := fun j hj => hiW (by rw [← hj]; exact mem_map_of_mem _ (mem_univ j))
  exact ⟨i, hiW', U i, ho, hUt i hiW'⟩

open Classical in
/-- An even class count in the window gives an even count outside it. -/
theorem tail_class_even {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    (D : List (Gen w)) (δ : ℕ) (hδ : δ + 1 ≤ lde (col s (pj s (piv_pos hs))))
    (hc : allSomeD P D δ = true)
    (htail : ∀ i, (∀ j, f j ≠ i) → ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i)
    (γ : Bool) (hcls : clsCount (w := w) (divAllD P D δ) γ 0 = true) :
    Even (univ.filter fun i => (∀ j, f j ≠ i) ∧ ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i ∧
      Odd y.re ∧ (Odd y.im ↔ γ = true)).card := by
  classical
  obtain ⟨U, hU, hUf, hUt⟩ := tail_numerators f hf hs hP D δ (by omega) hc htail
  set K := lde (col s (pj s (piv_pos hs))) - δ
  have hu : IsUnitVec (col (run (D.map (Gen.map f hf)) s) (pj s (piv_pos hs))) := col_unit _ _
  have hev := even_class_counts hu (K := K) (by omega) hU γ
  set W := univ.map (⟨f, hf.injective⟩ : Fin w ↪ Fin n)
  have hsplit := card_filter_split W fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)
  have hwin := card_cls f hf hUf hcls
  have heq : (univ.filter fun i => (∀ j, f j ≠ i) ∧ ∃ y, rt2 ^ δ * y =
      num (col s (pj s (piv_pos hs))) i ∧ Odd y.re ∧ (Odd y.im ↔ γ = true)) =
      (univ \ W).filter fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, W, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hi, y, hy, ho, hcl⟩
      have : U i = y := rt2_pow_mul_cancel (by rw [hUt i hi, hy])
      refine ⟨fun ⟨j, hj⟩ => hi j hj, ?_⟩
      rw [this]; exact ⟨ho, hcl⟩
    · rintro ⟨hi, ho, hcl⟩
      have hi' : ∀ j, f j ≠ i := fun j hj => hi ⟨j, hj⟩
      exact ⟨hi', U i, hUt i hi', ho, hcl⟩
  rw [heq]
  rw [hsplit] at hev
  rw [Nat.even_add] at hev
  exact hev.1 (Nat.even_iff.2 hwin)

end QCert.HadamardPi
