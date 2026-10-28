/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Transfers along words with `H` letters, and cleaning the tail

* `transfer_win`: a transfer along a word `K` on the window commuting with
  `A` and `B` (`Join.transfer_gen`), every state checked on the window.
* `clean_ind`: the entries outside the window `0, …, w-1` are divisible by
  `√2 ^ δ`; while two of them have depth exactly `δ` and the same class, the
  transfer along `H` on the two lowers both (Clément's Assumption 4 and the
  reductions of his Lemma 5.13, by his Lemma 5.3).  When no two remain, an
  even class count in the window (`tail_class_even`) leaves none, and the
  entries outside the window are divisible by `√2 ^ (δ + 1)`.
* `pow_ge_of_odd`: enough odd entries at an exponent bound it from below.
-/
import QCert.HadamardPi.SymNode

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### Exponents -/

theorem pow_ge_of_odd {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    (D : List (Gen w)) (δ : ℕ) (hδ : δ ≤ lde (col s (pj s (piv_pos hs))))
    (hc : allSomeD P D δ = true)
    (htail : ∀ i, (∀ j, f j ≠ i) → ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i) :
    ((List.range w).countP (fun j => oddSure ((divAllD P D δ).getD j dZ)) : ℤ) ≤
      2 ^ (lde (col s (pj s (piv_pos hs))) - δ) := by
  classical
  obtain ⟨U, hU, hUf, -⟩ := tail_numerators f hf hs hP D δ hδ hc htail
  have hu : IsUnitVec (col (run (D.map (Gen.map f hf)) s) (pj s (piv_pos hs))) := col_unit _ _
  have hsum := (sum_sq_components U (sum_sq_at hu hU)).1
  set S := (univ.filter fun j : Fin w => oddSure ((divAllD P D δ).getD j dZ) = true).map
    ⟨f, hf.injective⟩
  have hS : (S.card : ℤ) = ((List.range w).countP fun j => oddSure ((divAllD P D δ).getD j dZ)) := by
    rw [Finset.card_map, card_filter_univ_fin (fun j => oddSure ((divAllD P D δ).getD j dZ))]
  rw [← hS, ← hsum]
  have hnn : ∀ i, 0 ≤ (U i).re * (U i).re + 2 * ((U i).im * (U i).im) := fun i => by nlinarith
  calc (S.card : ℤ) = ∑ i ∈ S, (1 : ℤ) := by simp
    _ ≤ ∑ i ∈ S, ((U i).re * (U i).re + 2 * ((U i).im * (U i).im)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_map] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        rw [mem_filter] at hj
        have ho := odd_of_oddSure hj.2 t
        rw [← hUf] at ho
        obtain ⟨r, hr⟩ := ho
        have h0 : 0 ≤ (U (f j)).im * (U (f j)).im := mul_self_nonneg _
        have h1 : 0 ≤ r * r + r := by
          rcases le_or_gt 0 r with h | h
          · positivity
          · nlinarith
        have h2 : 1 ≤ (U (f j)).re * (U (f j)).re := by rw [hr]; nlinarith
        show (1 : ℤ) ≤ (U (f j)).re * (U (f j)).re + 2 * ((U (f j)).im * (U (f j)).im)
        linarith
    _ ≤ ∑ i, ((U i).re * (U i).re + 2 * ((U i).im * (U i).im)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hnn i

theorem one_le_of_pow {K : ℕ} {c : ℤ} (h : c ≤ 2 ^ K) (hc : 2 ≤ c) : 1 ≤ K := by
  rcases K with _ | K
  · simp at h; omega
  · omega

theorem two_le_of_pow {K : ℕ} {c : ℤ} (h : c ≤ 2 ^ K) (hc : 3 ≤ c) : 2 ≤ K := by
  rcases K with _ | _ | K
  · simp at h; omega
  · simp at h; omega
  · omega

/-! ### Commuting letters -/

/-- Letters on disjoint indices commute. -/
theorem comm2 (g g0 : Gen n) (h : ∀ i ∈ g.idx, ∀ i' ∈ g0.idx, i ≠ i') :
    Derivable Fig6 (ofList [g, g0]) (ofList [g0, g]) := by
  have m1 : ∀ a : Fin n, a ∈ (Gen.Z a : Gen n).idx := fun a => by simp [Gen.idx]
  have mXa : ∀ (a b : Fin n) (hab : a < b), a ∈ (Gen.X a b hab).idx := fun a b _ => by simp [Gen.idx]
  have mXb : ∀ (a b : Fin n) (hab : a < b), b ∈ (Gen.X a b hab).idx := fun a b _ => by simp [Gen.idx]
  have mHa : ∀ (a b : Fin n) (hab : a < b), a ∈ (Gen.H a b hab).idx := fun a b _ => by simp [Gen.idx]
  have mHb : ∀ (a b : Fin n) (hab : a < b), b ∈ (Gen.H a b hab).idx := fun a b _ => by simp [Gen.idx]
  cases g with
  | Z a =>
    cases g0 with
    | Z b => exact rl_b1 (h a (m1 a) b (m1 b))
    | X b c hbc =>
      exact rl_b2 hbc (h a (m1 a) b (mXa b c hbc)) (h a (m1 a) c (mXb b c hbc))
    | H b c hbc =>
      exact rl_b4 hbc (h a (m1 a) b (mHa b c hbc)) (h a (m1 a) c (mHb b c hbc))
  | X a b hab =>
    cases g0 with
    | Z c =>
      exact (rl_b2 hab (h a (mXa a b hab) c (m1 c)).symm (h b (mXb a b hab) c (m1 c)).symm).symm
    | X c d hcd =>
      exact rl_b3 hab hcd (h a (mXa a b hab) c (mXa c d hcd)) (h a (mXa a b hab) d (mXb c d hcd))
        (h b (mXb a b hab) c (mXa c d hcd)) (h b (mXb a b hab) d (mXb c d hcd))
    | H c d hcd =>
      exact rl_b5 hab hcd (h a (mXa a b hab) c (mHa c d hcd)) (h a (mXa a b hab) d (mHb c d hcd))
        (h b (mXb a b hab) c (mHa c d hcd)) (h b (mXb a b hab) d (mHb c d hcd))
  | H a b hab =>
    cases g0 with
    | Z c =>
      exact (rl_b4 hab (h a (mHa a b hab) c (m1 c)).symm (h b (mHb a b hab) c (m1 c)).symm).symm
    | X c d hcd =>
      exact (rl_b5 hcd hab (h a (mHa a b hab) c (mXa c d hcd)).symm
        (h b (mHb a b hab) c (mXa c d hcd)).symm (h a (mHa a b hab) d (mXb c d hcd)).symm
        (h b (mHb a b hab) d (mXb c d hcd)).symm).symm
    | H c d hcd =>
      exact rl_b6 hab hcd (h a (mHa a b hab) c (mHa c d hcd)) (h a (mHa a b hab) d (mHb c d hcd))
        (h b (mHb a b hab) c (mHa c d hcd)) (h b (mHb a b hab) d (mHb c d hcd))

/-- A letter commutes with a word on other indices. -/
theorem comm_letter (g0 : Gen n) :
    ∀ A : List (Gen n), (∀ g ∈ A, ∀ i ∈ g.idx, ∀ i' ∈ g0.idx, i ≠ i') →
      Derivable Fig6 (ofList (A ++ [g0])) (ofList ([g0] ++ A))
  | [], _ => Derivable.refl _
  | g :: A, h => by
    have ih := comm_letter g0 A (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    have step := comm2 g g0 (h g List.mem_cons_self)
    have e1 := der_mid [g] (A ++ [g0]) [] ([g0] ++ A) ih
    have e2 := der_mid [] [g, g0] A [g0, g] step
    simp only [List.append_nil, List.nil_append, List.cons_append] at e1 e2 ⊢
    exact e1.trans e2

/-! ### Transfers along a word on the window -/

/-- A transfer along a word `K` on the window commuting with `A` and `B`,
with the levels of `K s` and of the states of `K` from `A s` and `B s`
checked on the window. -/
theorem transfer_win {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
      zev (P.getD j dZ) t)
    {T : ℤ√2 → Prop}
    (htail : ∀ i : Fin n, w ≤ (i : ℕ) → T (num (col s (pj s (piv_pos hs))) i))
    {K A B : List (Gen w)}
    (hA : Derivable Fig6 (ofList (A ++ K)) (ofList (K ++ A)))
    (hB : Derivable Fig6 (ofList (B ++ K)) (ofList (K ++ B)))
    (hc : allSome P K = true) (j0 : Fin w) (ho : oddSure ((divAll P K).getD j0 dZ) = true)
    (hsame : sameOdd (w := w) P (divAll P K) = true)
    (hpA : pathOK P K A = true) (hpB : pathOK P K B = true)
    (hJ : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w ≤ piv s',
      (∀ j : Fin w, num (col s' (pj s' (piv_pos hs'))) (Fin.castLE (hw'.trans (piv_le_n s')) j) =
        zev ((divAll P K).getD j dZ) t) →
      (∀ i : Fin n, w ≤ (i : ℕ) → T (num (col s' (pj s' (piv_pos hs'))) i)) →
      Join s' (A.map (Gen.map (Fin.castLE (hw'.trans (piv_le_n s')))
          (Fin.strictMono_castLE (hw'.trans (piv_le_n s')))))
        (B.map (Gen.map (Fin.castLE (hw'.trans (piv_le_n s')))
          (Fin.strictMono_castLE (hw'.trans (piv_le_n s')))))) :
    Join s (A.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
      (B.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) := by
  set f := Fin.castLE (hw.trans (piv_le_n s))
  have hf : StrictMono f := Fin.strictMono_castLE _
  obtain ⟨hs', hpiv, hl, hwin, htl⟩ := pat_after f hf hs hk (castLE_lt hw) hP K hc j0 ho
  have hw' : w ≤ piv (run (K.map (Gen.map f hf)) s) := by rw [hpiv]; exact hw
  have hJ' := hJ _ hs' (by rw [hl]; exact hk) hw' hwin (fun i hi => by
    rw [htl i (fun j hj => by
      have := j.2; rw [← hj] at hi; simp [f] at hi; omega)]
    exact htail i hi)
  refine Join.transfer_gen (K := K.map (Gen.map f hf))
    (lev_after_eq f hf hs hk (castLE_lt hw) hP K hc j0 ho hsame).le ?_ ?_
    (path_of_check f hf hs hk (castLE_lt hw) hP hpA)
    (path_of_check f hf hs hk (castLE_lt hw) hP hpB) hJ'
  · have := der_map f hf hA; simpa only [List.map_append] using this
  · have := der_map f hf hB; simpa only [List.map_append] using this

/-! ### Cleaning the tail -/

/-- The window extended by two entries `x`, `y` outside it. -/
def fext {w : ℕ} (hwn : w ≤ n) (x y : Fin n) (j : Fin (w + 2)) : Fin n :=
  if h : (j : ℕ) < w then ⟨j, by omega⟩ else if (j : ℕ) = w then x else y

theorem fext_mono {w : ℕ} (hwn : w ≤ n) {x y : Fin n} (hx : w ≤ (x : ℕ)) (hxy : x < y) :
    StrictMono (fext hwn x y) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro j
  have hj := j.2
  have hxy' := Fin.lt_def.1 hxy
  simp only [fext, Fin.val_castSucc, Fin.val_succ, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

theorem fext_castLE {w : ℕ} (hwn : w ≤ n) (x y : Fin n) (j : Fin w) :
    fext hwn x y (Fin.castLE (by omega) j) = Fin.castLE hwn j := by
  simp [fext, Fin.ext_iff]

/-- The word `H_[w, w+1]` on the extended window. -/
def wordK2 (w : ℕ) : List (Gen (w + 2)) :=
  [Gen.H ⟨w, by omega⟩ ⟨w + 1, by omega⟩ (by simp [Fin.lt_def])]

/-- A word on the window, on the extended window. -/
def liftW {w : ℕ} (l : List (Gen w)) : List (Gen (w + 2)) :=
  l.map (Gen.map (Fin.castLE (by omega)) (Fin.strictMono_castLE _))

theorem liftW_map {w : ℕ} (hwn : w ≤ n) {x y : Fin n} (hf : StrictMono (fext hwn x y))
    (l : List (Gen w)) :
    (liftW l).map (Gen.map (fext hwn x y) hf) =
      l.map (Gen.map (Fin.castLE hwn) (Fin.strictMono_castLE hwn)) := by
  rw [liftW, List.map_map]
  congr 1
  funext g
  cases g <;> simp [Gen.map, fext_castLE]

/-- The pattern extended by two entries of depth `δ` and class `γ`. -/
def Pext2 (P : List ZL) (δ : ℕ) (γ : Bool) (nv : ℕ) : List ZL :=
  P ++ [dent δ γ nv, dent δ γ (nv + 2)]

/-- The checks of one cleaning step, for the class `γ`. -/
def cleanStepOK {w : ℕ} (P : List ZL) (nv δ : ℕ) (A0 B0 : List (Gen w)) (γ : Bool) : Bool :=
  allSome (Pext2 P δ γ nv) (wordK2 w) &&
    oddSure ((divAll (Pext2 P δ γ nv) (wordK2 w)).getD 0 dZ) &&
    sameOdd (w := w + 2) (Pext2 P δ γ nv) (divAll (Pext2 P δ γ nv) (wordK2 w)) &&
    pathOK (Pext2 P δ γ nv) (wordK2 w) (liftW A0) &&
    pathOK (Pext2 P δ γ nv) (wordK2 w) (liftW B0) &&
    decide (Pnorm ((divAll (Pext2 P δ γ nv) (wordK2 w)).take w) = Pnorm P) &&
    (zdivp (δ + 1) ((divAll (Pext2 P δ γ nv) (wordK2 w)).getD w dZ)).isSome &&
    (zdivp (δ + 1) ((divAll (Pext2 P δ γ nv) (wordK2 w)).getD (w + 1) dZ)).isSome

/-- The checks of the cleaning. -/
def cleanOK {w : ℕ} (P : List ZL) (nv δ : ℕ) (D A0 B0 : List (Gen w)) : Bool :=
  Pwidth P nv && decide (P.length = w) && decide (0 < w) && allSomeD P D δ &&
    clsCount (w := w) (divAllD P D δ) false 0 && clsCount (w := w) (divAllD P D δ) true 0 &&
    cleanStepOK P nv δ A0 B0 false && cleanStepOK P nv δ A0 B0 true

theorem castLE_ne_iff {w : ℕ} (h : w ≤ n) (i : Fin n) :
    (∀ j : Fin w, Fin.castLE h j ≠ i) ↔ w ≤ (i : ℕ) := by
  constructor
  · intro hi
    by_contra hlt
    exact hi ⟨i, by omega⟩ (Fin.ext rfl)
  · intro hi j hj
    have := congrArg Fin.val hj
    simp at this
    omega

theorem dent_eval (δ : ℕ) {γ : Bool} (nv : ℕ) (t : ℕ → ℤ) {y : ℤ√2} (hyo : Odd y.re)
    (hyc : Odd y.im ↔ γ = true) :
    zev (dent δ γ nv) (text t nv ((y.re - 1) / 2) ((y.im - (if γ then 1 else 0)) / 2)) =
      rt2 ^ δ * y := by
  rw [zev_dent]
  congr 1
  simp only [text, if_pos rfl, if_neg (show nv + 1 ≠ nv by omega)]
  obtain ⟨r, hr⟩ := hyo
  apply Zsqrtd.ext
  · show 1 + 2 * ((y.re - 1) / 2) = y.re; omega
  · show (if γ then 1 else 0) + 2 * ((y.im - (if γ then 1 else 0)) / 2) = y.im
    cases γ
    · simp only [Bool.false_eq_true, if_false, iff_false, Int.not_odd_iff_even] at hyc ⊢
      obtain ⟨m, hm⟩ := hyc; omega
    · simp only [if_true, iff_true] at hyc ⊢
      obtain ⟨m, hm⟩ := hyc; omega

theorem Pwidth_dent (δ : ℕ) (γ : Bool) (nv : ℕ) : Pwidth [dent δ γ nv] (nv + 2) = true := by
  have key : ∀ (d : ℕ) (x : ZL), x.1.length ≤ nv + 3 → x.2.length ≤ nv + 3 →
      (zrt2^[d] x).1.length ≤ nv + 3 ∧ (zrt2^[d] x).2.length ≤ nv + 3 := by
    intro d
    induction d with
    | zero => intro x h1 h2; exact ⟨h1, h2⟩
    | succ d ih =>
      intro x h1 h2
      rw [Function.iterate_succ_apply]
      exact ih _ (by simp only [zrt2, length_lsmul]; exact h2) (by simpa [zrt2] using h1)
  obtain ⟨h1, h2⟩ := key δ (dbase γ nv) (by simp [dbase]) (by simp [dbase])
  simp [Pwidth, dent, h1, h2]

theorem even_card_le_one {α : Type*} (S : Finset α) (h1 : Even S.card)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, a = b) (a : α) (ha : a ∈ S) : False := by
  have hle := Finset.card_le_one.2 h2
  have hpos := Finset.card_pos.2 ⟨a, ha⟩
  obtain ⟨r, hr⟩ := h1
  omega

/-- Cleaning the tail at depth `δ`. -/
theorem clean_ind {w : ℕ} {P : List ZL} {nv δ : ℕ} {D A0 B0 : List (Gen w)}
    (hok : cleanOK P nv δ D A0 B0 = true)
    (step : ∀ (s : O n) (hs : s ≠ 1), lde (col s (pj s (piv_pos hs))) ≠ 0 →
      ∀ hw : w ≤ piv s, δ + 1 ≤ lde (col s (pj s (piv_pos hs))) → ∀ t : ℕ → ℤ,
      (∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
        zev (P.getD j dZ) t) →
      (∀ i : Fin n, w ≤ (i : ℕ) → ∃ y, rt2 ^ (δ + 1) * y = num (col s (pj s (piv_pos hs))) i) →
      Join s (A0.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
          (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
        (B0.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
          (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))) :
    ∀ (s : O n) (hs : s ≠ 1), lde (col s (pj s (piv_pos hs))) ≠ 0 →
      ∀ hw : w ≤ piv s, δ + 1 ≤ lde (col s (pj s (piv_pos hs))) → ∀ t : ℕ → ℤ,
      (∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
        zev (P.getD j dZ) t) →
      (∀ i : Fin n, w ≤ (i : ℕ) → ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i) →
      Join s (A0.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
          (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
        (B0.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
          (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) := by
  classical
  simp only [cleanOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hPw, hPl⟩, hw0⟩, hcD⟩, hc0⟩, hc1⟩, hstep0⟩, hstep1⟩ := hok
  -- the measure: entries outside the window of depth exactly `δ`
  let μ : (s : O n) → (hs : s ≠ 1) → ℕ := fun s hs =>
    (univ.filter fun i : Fin n => w ≤ (i : ℕ) ∧
      ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i ∧ Odd y.re).card
  suffices H : ∀ m (s : O n) (hs : s ≠ 1), μ s hs = m → lde (col s (pj s (piv_pos hs))) ≠ 0 →
      ∀ hw : w ≤ piv s, δ + 1 ≤ lde (col s (pj s (piv_pos hs))) → ∀ t : ℕ → ℤ,
      (∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
        zev (P.getD j dZ) t) →
      (∀ i : Fin n, w ≤ (i : ℕ) → ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i) →
      Join s (A0.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
          (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
        (B0.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
          (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) from
    fun s hs hk hw hδ t hP htail => H _ s hs rfl hk hw hδ t hP htail
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro s hs hm hk hw hδ t hP htail
  set v := col s (pj s (piv_pos hs)) with hv
  have hwn : w ≤ n := hw.trans (piv_le_n s)
  by_cases hpair : ∃ (x y : Fin n) (γ : Bool) (yx yy : ℤ√2), w ≤ (x : ℕ) ∧ x < y ∧
      rt2 ^ δ * yx = num v x ∧ Odd yx.re ∧ (Odd yx.im ↔ γ = true) ∧
      rt2 ^ δ * yy = num v y ∧ Odd yy.re ∧ (Odd yy.im ↔ γ = true)
  · obtain ⟨x, y, γ, yx, yy, hx, hxy, hyx, hox, hcx, hyy, hoy, hcy⟩ := hpair
    have hstep : cleanStepOK P nv δ A0 B0 γ = true := by cases γ <;> assumption
    simp only [cleanStepOK, Bool.and_eq_true, decide_eq_true_eq] at hstep
    obtain ⟨⟨⟨⟨⟨⟨⟨hcK, hoK⟩, hsK⟩, hpA⟩, hpB⟩, htake⟩, hdx⟩, hdy⟩ := hstep
    set f := fext hwn x y
    have hf : StrictMono f := fext_mono hwn hx hxy
    have hxJ : (x : ℕ) < piv s := idx_lt_piv_of_num hs (by
      rw [← hyx]; exact rt2_pow_mul_ne_zero (odd_ne_zero hox))
    have hyJ : (y : ℕ) < piv s := idx_lt_piv_of_num hs (by
      rw [← hyy]; exact rt2_pow_mul_ne_zero (odd_ne_zero hoy))
    have hfJ : ∀ j, (f j : ℕ) < piv s := by
      intro j; simp only [f, fext]
      split_ifs with h1 h2
      · show (j : ℕ) < piv s; omega
      · exact hxJ
      · exact hyJ
    set t1 := text t nv ((yx.re - 1) / 2) ((yx.im - (if γ then 1 else 0)) / 2)
    set t' := text t1 (nv + 2) ((yy.re - 1) / 2) ((yy.im - (if γ then 1 else 0)) / 2)
    have hdent1 : zev (dent δ γ nv) t' = num v x := by
      rw [← hyx, ← dent_eval δ nv t hox hcx]
      exact zev_congr (P := [dent δ γ nv]) (Pwidth_dent δ γ nv)
        (fun i hi => by simp only [t', t1, text]; split_ifs <;> first | rfl | omega) 0
    have hdent2 : zev (dent δ γ (nv + 2)) t' = num v y := by
      rw [← hyy, ← dent_eval δ (nv + 2) t1 hoy hcy]
    have hPt : ∀ j : ℕ, j < w → zev (P.getD j dZ) t' = zev (P.getD j dZ) t := by
      intro j hj
      exact zev_congr hPw (fun i hi => by
        simp only [t', t1, text]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]) j
    have hP' : ∀ j : Fin (w + 2), num v (f j) = zev ((Pext2 P δ γ nv).getD j dZ) t' := by
      intro j
      simp only [Pext2, List.getD_eq_getElem?_getD]
      by_cases h1 : (j : ℕ) < w
      · rw [List.getElem?_append_left (by rw [hPl]; exact h1), ← List.getD_eq_getElem?_getD,
          hPt j h1]
        have : f j = Fin.castLE hwn ⟨j, h1⟩ := by simp [f, fext, h1, Fin.ext_iff]
        rw [this, hP ⟨j, h1⟩]
      · rw [List.getElem?_append_right (by rw [hPl]; omega), hPl]
        by_cases h2 : (j : ℕ) = w
        · have : f j = x := by simp [f, fext, h2]
          rw [this, h2, Nat.sub_self]; simpa using hdent1.symm
        · have hj : (j : ℕ) = w + 1 := by have := j.2; omega
          have : f j = y := by simp [f, fext, h2, hj]
          rw [this, hj, show w + 1 - w = 1 by omega]; simpa using hdent2.symm
    obtain ⟨hs', hpiv, hl, hwin, htl⟩ := pat_after f hf hs hk hfJ hP' (wordK2 w) hcK 0 hoK
    have hK1 : (wordK2 w).map (Gen.map f hf) = [Gen.H x y hxy] := by
      simp [wordK2, Gen.map, f, fext]
    have hcomm : ∀ L : List (Gen w), Derivable Fig6
        (ofList (L.map (Gen.map (Fin.castLE hwn) (Fin.strictMono_castLE hwn)) ++
          (wordK2 w).map (Gen.map f hf)))
        (ofList ((wordK2 w).map (Gen.map f hf) ++
          L.map (Gen.map (Fin.castLE hwn) (Fin.strictMono_castLE hwn)))) := by
      intro L
      rw [hK1]
      refine comm_letter _ _ fun g hg i hi i' hi' => ?_
      rw [List.mem_map] at hg
      obtain ⟨g0, -, rfl⟩ := hg
      obtain ⟨j, rfl⟩ := idx_map _ _ g0 hi
      simp only [Gen.idx, mem_insert, mem_singleton] at hi'
      intro h
      rcases hi' with rfl | rfl
      · have := congrArg Fin.val h; simp at this; omega
      · have := congrArg Fin.val h; simp at this; have := j.2; omega
    -- the new state
    set s'' := run ((wordK2 w).map (Gen.map f hf)) s
    have hw'' : w ≤ piv s'' := by rw [hpiv]; exact hw
    have hP'' : ∀ j : Fin w, num (col s'' (pj s'' (piv_pos hs'))) (Fin.castLE (hw''.trans
        (piv_le_n s'')) j) = zev (P.getD j dZ) t := by
      intro j
      have e1 : Fin.castLE (hw''.trans (piv_le_n s'')) j = f (Fin.castLE (by omega) j) :=
        (fext_castLE hwn x y j).symm
      rw [e1, hwin]
      have h1 : (divAll (Pext2 P δ γ nv) (wordK2 w)).getD (Fin.castLE (by omega) j : Fin (w + 2))
          dZ = ((divAll (Pext2 P δ γ nv) (wordK2 w)).take w).getD j dZ := by
        simp only [Fin.coe_castLE, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos j.2]
      rw [h1, ← zev_Pnorm, htake, zev_Pnorm, hPt j j.2]
    have hnew : ∀ j : Fin (w + 2), w ≤ (j : ℕ) →
        ∃ z, rt2 ^ (δ + 1) * z = num (col s'' (pj s'' (piv_pos hs'))) (f j) := by
      intro j hj
      rw [hwin]
      have hsome : (zdivp (δ + 1) ((divAll (Pext2 P δ γ nv) (wordK2 w)).getD j dZ)).isSome := by
        by_cases h2 : (j : ℕ) = w
        · rw [h2]; exact hdx
        · rw [show (j : ℕ) = w + 1 by have := j.2; omega]; exact hdy
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hsome
      exact ⟨zev z t', zdivp_sound _ hz t'⟩
    have hfx : f ⟨w, by omega⟩ = x := by simp [f, fext]
    have hfy : f ⟨w + 1, by omega⟩ = y := by simp [f, fext]
    have hout : ∀ i : Fin n, w ≤ (i : ℕ) → i ≠ x → i ≠ y → ∀ j, f j ≠ i := by
      intro i hi hix hiy j hj
      simp only [f, fext] at hj
      split_ifs at hj with h1 h2
      · have := congrArg Fin.val hj; simp at this; omega
      · exact hix hj.symm
      · exact hiy hj.symm
    have notodd : ∀ j : Fin (w + 2), w ≤ (j : ℕ) → ∀ z,
        rt2 ^ δ * z = num (col s'' (pj s'' (piv_pos hs'))) (f j) → ¬Odd z.re := by
      intro j hj z hz hzo
      obtain ⟨z', hz'⟩ := hnew j hj
      rw [← hz, pow_succ, mul_assoc] at hz'
      have := rt2_pow_mul_cancel hz'
      rw [← this, rt2_mul] at hzo
      obtain ⟨r, hr⟩ := hzo
      dsimp only at hr
      omega
    have htail'' : ∀ i : Fin n, w ≤ (i : ℕ) →
        ∃ z, rt2 ^ δ * z = num (col s'' (pj s'' (piv_pos hs'))) i := by
      intro i hi
      by_cases hix : i = x
      · obtain ⟨z, hz⟩ := hnew ⟨w, by omega⟩ le_rfl
        rw [hfx, ← hix] at hz
        exact ⟨rt2 * z, by rw [← hz, pow_succ]; ring⟩
      by_cases hiy : i = y
      · obtain ⟨z, hz⟩ := hnew ⟨w + 1, by omega⟩ (by simp)
        rw [hfy, ← hiy] at hz
        exact ⟨rt2 * z, by rw [← hz, pow_succ]; ring⟩
      rw [htl i (hout i hi hix hiy)]; exact htail i hi
    -- the measure goes down
    have hlt : μ s'' hs' < m := by
      rw [← hm]
      apply Finset.card_lt_card
      refine ⟨fun i hi => ?_, fun hsub => ?_⟩
      · simp only [mem_filter, mem_univ, true_and] at hi ⊢
        obtain ⟨hiw, z, hz, hzo⟩ := hi
        refine ⟨hiw, ?_⟩
        by_cases hix : i = x
        · exact absurd hzo (notodd ⟨w, by omega⟩ le_rfl z (by rw [hfx, ← hix]; exact hz))
        by_cases hiy : i = y
        · exact absurd hzo (notodd ⟨w + 1, by omega⟩ (by simp) z (by rw [hfy, ← hiy]; exact hz))
        rw [htl i (hout i hiw hix hiy)] at hz
        exact ⟨z, hz, hzo⟩
      · have hxm : x ∈ univ.filter fun i : Fin n => w ≤ (i : ℕ) ∧
            ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i ∧ Odd y.re := by
          simp only [mem_filter, mem_univ, true_and]; exact ⟨hx, yx, hyx, hox⟩
        have := hsub hxm
        simp only [mem_filter, mem_univ, true_and] at this
        obtain ⟨-, z, hz, hzo⟩ := this
        exact notodd ⟨w, by omega⟩ le_rfl z (by rw [hfx]; exact hz) hzo
    have hJ'' := ih _ hlt s'' hs' rfl (by rw [hl]; exact hk) hw'' (by rw [hl]; exact hδ) t hP''
      htail''
    refine Join.transfer_gen (K := (wordK2 w).map (Gen.map f hf))
      (lev_after_eq f hf hs hk hfJ hP' (wordK2 w) hcK 0 hoK hsK).le (hcomm A0) (hcomm B0) ?_ ?_ hJ''
    · have := path_of_check f hf hs hk hfJ hP' hpA
      rwa [liftW_map] at this
    · have := path_of_check f hf hs hk hfJ hP' hpB
      rwa [liftW_map] at this
  · -- no two entries of depth `δ` and one class: none at all
    have hcast : StrictMono (Fin.castLE hwn) := Fin.strictMono_castLE hwn
    have htail' : ∀ i, (∀ j : Fin w, Fin.castLE hwn j ≠ i) → ∃ y, rt2 ^ δ * y = num v i :=
      fun i hi => htail i ((castLE_ne_iff hwn i).1 hi)
    have hnone : ∀ γ : Bool, ∀ i : Fin n, w ≤ (i : ℕ) → ∀ y, rt2 ^ δ * y = num v i → Odd y.re →
        ¬(Odd y.im ↔ γ = true) := by
      intro γ i hi y hy hyo hyc
      have hev := tail_class_even (Fin.castLE hwn) hcast hs hP D δ hδ hcD htail' γ
        (by cases γ <;> assumption)
      refine even_card_le_one _ hev (fun a ha b hb => ?_) i ?_
      · simp only [mem_filter, mem_univ, true_and] at ha hb
        obtain ⟨ha1, ya, hya, hoa, hca⟩ := ha
        obtain ⟨hb1, yb, hyb, hob, hcb⟩ := hb
        rw [castLE_ne_iff] at ha1 hb1
        by_contra hab
        rcases lt_or_gt_of_ne hab with h | h
        · exact hpair ⟨a, b, γ, ya, yb, ha1, h, hya, hoa, hca, hyb, hob, hcb⟩
        · exact hpair ⟨b, a, γ, yb, ya, hb1, h, hyb, hob, hcb, hya, hoa, hca⟩
      · simp only [mem_filter, mem_univ, true_and]
        exact ⟨(castLE_ne_iff hwn i).2 hi, y, hy, hyo, hyc⟩
    refine step s hs hk hw hδ t hP fun i hi => ?_
    obtain ⟨y, hy⟩ := htail i hi
    have hye : ¬Odd y.re := fun hyo =>
      hnone (decide (Odd y.im)) i hi y hy hyo (by simp)
    rw [Int.not_odd_iff_even] at hye
    obtain ⟨r, hr⟩ := hye
    refine ⟨⟨y.im, r⟩, ?_⟩
    rw [pow_succ, mul_assoc, rt2_mul, ← hy]
    congr 1
    apply Zsqrtd.ext <;> simp <;> omega

end QCert.HadamardPi
