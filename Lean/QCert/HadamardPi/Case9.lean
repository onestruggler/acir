/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Main Case 9 (2)(b): `H_[0,1]` on two odd entries of different classes

The state `s` has odd numerators at `0` and `1` of different classes, so
`r = H_[0,1] s` has the same level (`hv_odd_diff`): its entries `0` and `1`
are again odd of different classes, the others unchanged.  The first
syllables are `N = H_[0,P]` and `N' = H_[0,P']`, with `P`, `P'` the
partners of `0` in `s` and in `r`.

* With more than four odd entries there is a matched pair `E` of `s` away
  from `0, 1, P, P'` (the classes have evenly many odd entries), and the
  square closes by the diamond `H_E H_[0,P'] H_[0,1] H_[0,P] H_E`: every
  state on it is below `s` (`case9_many`).
* With exactly four odd entries (Clément's Case 3.4) the square needs
  entries outside the four odd ones (see the README); this is `Case9Four`,
  proved in `CaseFour.lean`.
-/
import QCert.HadamardPi.Confluence

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### `H` on two odd entries of different classes -/

theorem hv_odd_diff {v : Fin n → ℝ} (hR : InRing v) {z o : Fin n} (hzo : z ≠ o)
    (hz : Odd (num v z).re) (ho : Odd (num v o).re) (hd : ¬SameOdd (num v z) (num v o)) :
    lde (hv z o v) = lde v ∧ (∀ i, i ≠ z → i ≠ o → num (hv z o v) i = num v i) ∧
      Odd (num (hv z o v) z).re ∧ Odd (num (hv z o v) o).re ∧
      ¬SameOdd (num (hv z o v) z) (num (hv z o v) o) ∧
      num (hv z o v) z = ⟨(num v z).im + (num v o).im, ((num v z).re + (num v o).re) / 2⟩ := by
  classical
  set k := lde v
  have hz' := toReal_num hR z
  have ho' := toReal_num hR o
  have hzr := Int.odd_iff.1 hz
  have hor := Int.odd_iff.1 ho
  have him : (num v z).im % 2 ≠ (num v o).im % 2 := by
    intro h
    exact hd ⟨hz, ho, by rw [Int.odd_iff, Int.odd_iff, h]⟩
  set n1 : ℤ√2 := ⟨(num v z).im + (num v o).im, ((num v z).re + (num v o).re) / 2⟩ with hn1
  set n2 : ℤ√2 := ⟨(num v z).im - (num v o).im, ((num v z).re - (num v o).re) / 2⟩ with hn2
  have e1 : rt2 * n1 = num v z + num v o := by
    rw [rt2_mul]; ext <;> simp only [hn1, Zsqrtd.re_add, Zsqrtd.im_add] <;> omega
  have e2 : rt2 * n2 = num v z - num v o := by
    rw [rt2_mul]; ext <;> simp only [hn2, Zsqrtd.re_sub, Zsqrtd.im_sub] <;> omega
  have hcancel : ∀ {m : ℤ√2} {y : ℝ}, toReal (rt2 * m) = Real.sqrt 2 ^ k * y →
      toReal m = Real.sqrt 2 ^ k * (invSqrt2 * y) := by
    intro m y h
    rw [map_mul, toReal_rt2] at h
    have hs := sqrt2_mul_invSqrt2
    apply mul_left_cancel₀ sqrt2_ne_zero
    rw [h]
    linear_combination (-(Real.sqrt 2 ^ k * y)) * hs
  set u : Fin n → ℤ√2 := fun i => if i = z then n1 else if i = o then n2 else num v i with hu
  have hu' : ∀ i, toReal (u i) = Real.sqrt 2 ^ k * hv z o v i := by
    intro i
    simp only [hu, hv]
    split_ifs with h1 h2
    · exact hcancel (by rw [e1, map_add, hz', ho']; ring)
    · exact hcancel (by rw [e2, map_sub, hz', ho']; ring)
    · exact toReal_num hR i
  have hR' : InRing (hv z o v) := fun i => by
    simp only [hv]
    split_ifs
    · exact ZInvSqrt2.mul_mem invSqrt2_mem (ZInvSqrt2.add_mem (hR z) (hR o))
    · exact ZInvSqrt2.mul_mem invSqrt2_mem (ZInvSqrt2.sub_mem (hR z) (hR o))
    · exact hR i
  have huz : u z = n1 := by simp [hu]
  have huo : u o = n2 := by simp [hu, Ne.symm hzo]
  have hn1odd : Odd n1.re := Int.odd_iff.2 (by simp only [hn1]; omega)
  have hn2odd : Odd n2.re := Int.odd_iff.2 (by simp only [hn2]; omega)
  have hl : lde (hv z o v) = k := by
    refine le_antisymm (lde_le fun i => ⟨u i, hu' i⟩) (not_lt.1 fun hlt => ?_)
    obtain ⟨K, hK⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hden := (denV_lde hR').mono (k' := K) (by omega) z
    have := hu' z
    rw [huz, hK] at this
    exact not_den_of_odd this hn1odd hden
  have hnum : num (hv z o v) = u := num_eq hR' (by rw [hl]; exact hu')
  refine ⟨hl, fun i h1 h2 => by rw [hnum]; simp [hu, h1, h2], by rw [hnum, huz]; exact hn1odd,
    by rw [hnum, huo]; exact hn2odd, ?_, by rw [hnum, huz, hn1]⟩
  rw [hnum, huz, huo]
  rintro ⟨-, -, hiff⟩
  rw [Int.odd_iff, Int.odd_iff] at hiff
  simp only [hn1, hn2] at hiff
  by_cases h : ((num v z).re + (num v o).re) / 2 % 2 = 1
  · have := hiff.1 h; omega
  · have : ¬((num v z).re - (num v o).re) / 2 % 2 = 1 := fun h' => h (hiff.2 h')
    omega

/-! ### The state `r = H_[0,1] s` -/

theorem sem_comm_H {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (u : O n) :
    sem n (Gen.H a b hab) * (sem n (Gen.H c d hcd) * u) =
      sem n (Gen.H c d hcd) * (sem n (Gen.H a b hab) * u) := by
  have := run_eq_of_der (rl_b6 hab hcd hac had hbc hbd) u
  simpa [run_cons, run_nil] using this

/-- With more than four odd entries: the diamond through a matched pair `E`
away from the square. -/
theorem case9_diamond {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    {z o P P' e1 e2 : Fin n} (hzo : z < o) (hzP : z < P) (hzP' : z < P') (he : e1 < e2)
    (hr : sem n (Gen.H z o hzo) * s ≠ 1)
    (hkr : lde (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) ≠ 0)
    (hpiv : piv (sem n (Gen.H z o hzo) * s) = piv s)
    (hlev : lev (sem n (Gen.H z o hzo) * s) = lev s)
    (hsyl : syl s = FreeMonoid.of (Gen.H z P hzP))
    (hsylr : syl (sem n (Gen.H z o hzo) * s) = FreeMonoid.of (Gen.H z P' hzP'))
    (hPJ : (P : ℕ) < piv s) (hP'J : (P' : ℕ) < piv s) (he2J : (e2 : ℕ) < piv s)
    (hA : SameOdd (num (col s (pj s (piv_pos hs))) z) (num (col s (pj s (piv_pos hs))) P))
    (hE : SameOdd (num (col s (pj s (piv_pos hs))) e1) (num (col s (pj s (piv_pos hs))) e2))
    (hA' : SameOdd (num (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) z)
      (num (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) P'))
    (hEr : SameOdd (num (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) e1)
      (num (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) e2))
    (h1z : e1 ≠ z) (h1o : e1 ≠ o) (h1P : e1 ≠ P) (h1P' : e1 ≠ P')
    (h2z : e2 ≠ z) (h2o : e2 ≠ o) (h2P : e2 ≠ P) (h2P' : e2 ≠ P') :
    MainSquare s (Gen.H z o hzo) := by
  have hp := piv_pos hs
  set r := sem n (Gen.H z o hzo) * s with hrdef
  have hpr := piv_pos hr
  set A := Gen.H z P hzP
  set A' := Gen.H z P' hzP'
  set G := Gen.H z o hzo
  set E := Gen.H e1 e2 he
  -- `E` commutes with `A`, `A'`, `G`
  have cA : ∀ u : O n, sem n E * (sem n A * u) = sem n A * (sem n E * u) :=
    sem_comm_H he hzP h1z h1P h2z h2P
  have cA' : ∀ u : O n, sem n E * (sem n A' * u) = sem n A' * (sem n E * u) :=
    sem_comm_H he hzP' h1z h1P' h2z h2P'
  have cG : ∀ u : O n, sem n E * (sem n G * u) = sem n G * (sem n E * u) :=
    sem_comm_H he hzo h1z h1o h2z h2o
  have he2J' : (e2 : ℕ) < piv r := by rw [hpiv]; exact he2J
  have hP'J' : (P' : ℕ) < piv r := by rw [hpiv]; exact hP'J
  -- the derivation `A' G ≈ (E A' G A E) A`
  have hder : Derivable Fig6 (syl r * FreeMonoid.of G) (ofList [E, A', G, A, E] * syl s) := by
    rw [hsylr, hsyl]
    show Derivable Fig6 (ofList [A', G]) (ofList [E, A', G, A, E, A])
    refine Derivable.symm ?_
    exact (rw_at [E, A', G, A, E, A] 3 (rl_b6 hzP he (Ne.symm h1z) (Ne.symm h2z) (Ne.symm h1P)
        (Ne.symm h2P)) rfl).trans <|
      (rw_at _ 4 (rl_a3 hzP) rfl).trans <|
      (rw_at _ 2 (rl_b6 hzo he (Ne.symm h1z) (Ne.symm h2z) (Ne.symm h1o) (Ne.symm h2o)) rfl).trans <|
      (rw_at _ 1 (rl_b6 hzP' he (Ne.symm h1z) (Ne.symm h2z) (Ne.symm h1P') (Ne.symm h2P')) rfl).trans <|
      (rw_at _ 0 (rl_a3 he) rfl)
  refine square_of hs hr [E, A', G, A, E] ?_ hder
  rw [hsyl, FreeMonoid.lift_eval_of]
  -- the states
  have L0 : lev (sem n A * s) < lev s := lev_pair_lt hp hzP hPJ hk hA
  have L1 : lev (sem n E * (sem n A * s)) < lev s :=
    lev_two_pairs hs hk hzP he hPJ he2J hA hE h1z h1P h2z h2P
  have L2 : lev (sem n E * s) < lev s := lev_pair_lt hp he he2J hk hE
  have L3 : lev (sem n E * r) < lev s := hlev ▸ lev_pair_lt hpr he he2J' hkr hEr
  have L4 : lev (sem n E * (sem n A' * r)) < lev s :=
    hlev ▸ lev_two_pairs hr hkr hzP' he hP'J' he2J' hA' hEr h1z h1P' h2z h2P'
  have L5 : lev (sem n A' * r) < lev s := by
    have := lev_syl_lt hr
    rw [hsylr, FreeMonoid.lift_eval_of] at this
    exact hlev ▸ this
  refine ⟨⟨⟨⟨⟨L0, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp only [run_cons, run_nil]
  · exact L1
  · rw [← cA, sem_sq_assoc]; exact L2
  · rw [← cA, sem_sq_assoc, ← cG]; exact L3
  · rw [← cA, sem_sq_assoc, ← cG, ← cA']; exact L4
  · rw [← cA, sem_sq_assoc, ← cG, ← cA', sem_sq_assoc]; exact L5

/-! ### Classes -/

theorem same_of_not_not {a b c : ℤ√2} (hb : Odd b.re) (hc : Odd c.re)
    (hab : ¬SameOdd a b) (hac : ¬SameOdd a c) (ha : Odd a.re) : SameOdd b c := by
  refine ⟨hb, hc, ?_⟩
  have e1 : ¬(Odd a.im ↔ Odd b.im) := fun h => hab ⟨ha, hb, h⟩
  have e2 : ¬(Odd a.im ↔ Odd c.im) := fun h => hac ⟨ha, hc, h⟩
  tauto

theorem pair_of_two {S : Finset (Fin n)} (h : 1 < S.card) :
    ∃ e1 e2, e1 ∈ S ∧ e2 ∈ S ∧ e1 < e2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
  rcases lt_or_gt_of_ne hab with h' | h'
  · exact ⟨a, b, ha, hb, h'⟩
  · exact ⟨b, a, hb, ha, h'⟩

open Classical in
/-- With more than four odd entries, a matched pair away from `z, o, P, P'`. -/
theorem exists_far_pair {v : Fin n → ℝ} (hR : InRing v) (hU : IsUnitVec v) (hk : lde v ≠ 0)
    {z o P P' : Fin n} (hz : Odd (num v z).re) (ho : Odd (num v o).re)
    (hzo : ¬SameOdd (num v z) (num v o)) (hzP : z ≠ P) (hP : SameOdd (num v z) (num v P))
    (hP' : P' = P ∨ (P' ≠ o ∧ SameOdd (num v o) (num v P')))
    (hl : (oddSet v).card ≠ 4) :
    ∃ e1 e2 : Fin n, e1 < e2 ∧ SameOdd (num v e1) (num v e2) ∧
      e1 ≠ z ∧ e1 ≠ o ∧ e1 ≠ P ∧ e1 ≠ P' ∧ e2 ≠ z ∧ e2 ≠ o ∧ e2 ≠ P ∧ e2 ≠ P' := by
  set Cz := univ.filter fun i => SameOdd (num v z) (num v i) with hCz
  set Co := univ.filter fun i => SameOdd (num v o) (num v i) with hCo
  have evz : Even Cz.card := even_card_class hR hU hk hz
  have evo : Even Co.card := even_card_class hR hU hk ho
  have hdisj : Disjoint Cz Co := by
    rw [hCz, hCo, disjoint_filter]
    intro i _ h1 h2
    exact hzo (h1.trans h2.symm)
  have hunion : Cz ∪ Co = oddSet v := by
    ext i
    simp only [hCz, hCo, mem_union, mem_filter, mem_univ, true_and, mem_oddSet]
    constructor
    · rintro (h | h)
      · exact h.2.1
      · exact h.2.1
    · intro hi
      by_cases h : SameOdd (num v z) (num v i)
      · exact Or.inl h
      · exact Or.inr (same_of_not_not ho hi hzo h hz)
  have hcard : Cz.card + Co.card = (oddSet v).card := by
    rw [← hunion, card_union_of_disjoint hdisj]
  have hev := even_card_oddSet hR hU (Nat.one_le_iff_ne_zero.2 hk)
  have hzC : z ∈ Cz := by rw [hCz, mem_filter]; exact ⟨mem_univ _, SameOdd.refl hz⟩
  have hPC : P ∈ Cz := by rw [hCz, mem_filter]; exact ⟨mem_univ _, hP⟩
  have hoC : o ∈ Co := by rw [hCo, mem_filter]; exact ⟨mem_univ _, SameOdd.refl ho⟩
  have hoCz : o ∉ Cz := fun h => disjoint_left.1 hdisj h hoC
  have hPCo : P ∉ Co := fun h => disjoint_left.1 hdisj hPC h
  have hzCo : z ∉ Co := fun h => disjoint_left.1 hdisj hzC h
  set Sz := (Cz.erase z).erase P with hSz
  have hSzc : Sz.card = Cz.card - 2 := by
    rw [hSz, card_erase_of_mem (mem_erase.2 ⟨Ne.symm hzP, hPC⟩), card_erase_of_mem hzC]; omega
  have hSz_mem : ∀ e ∈ Sz, e ∈ Cz ∧ e ≠ z ∧ e ≠ P := by
    intro e he; simp only [hSz, mem_erase] at he; exact ⟨he.2.2, he.2.1, he.1⟩
  have hCz2 : 2 ≤ Cz.card := by
    have := card_le_card (show ({z, P} : Finset (Fin n)) ⊆ Cz by
      intro i hi; simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hzC
      · exact hPC)
    rwa [card_pair hzP] at this
  have hCo1 : 1 ≤ Co.card := card_pos.2 ⟨o, hoC⟩
  have pairIn : ∀ S : Finset (Fin n),
      ((∀ e ∈ S, e ∈ Cz) ∨ (∀ e ∈ S, e ∈ Co)) → 1 < S.card →
      ∃ e1 e2, e1 ∈ S ∧ e2 ∈ S ∧ e1 < e2 ∧ SameOdd (num v e1) (num v e2) := by
    intro S hS h2
    obtain ⟨e1, e2, h1, h2', h12⟩ := pair_of_two h2
    refine ⟨e1, e2, h1, h2', h12, ?_⟩
    rcases hS with hS | hS
    · have a1 := hS e1 h1
      have a2 := hS e2 h2'
      rw [hCz, mem_filter] at a1 a2
      exact a1.2.symm.trans a2.2
    · have a1 := hS e1 h1
      have a2 := hS e2 h2'
      rw [hCo, mem_filter] at a1 a2
      exact a1.2.symm.trans a2.2
  rcases hP' with rfl | ⟨hP'o, hP'C⟩
  · -- `P' = P`: `Cz` minus `z, P`, or `Co` minus `o`
    set So := Co.erase o with hSo
    have hSoc : So.card = Co.card - 1 := by rw [hSo, card_erase_of_mem hoC]
    have hSo_mem : ∀ e ∈ So, e ∈ Co ∧ e ≠ o := by
      intro e he; simp only [hSo, mem_erase] at he; exact ⟨he.2, he.1⟩
    by_cases hb : 1 < Sz.card
    · obtain ⟨e1, e2, h1, h2, h12, hs⟩ := pairIn Sz (Or.inl fun e he => (hSz_mem e he).1) hb
      obtain ⟨c1, n1z, n1P⟩ := hSz_mem e1 h1
      obtain ⟨c2, n2z, n2P⟩ := hSz_mem e2 h2
      exact ⟨e1, e2, h12, hs, n1z, fun h => hoCz (h ▸ c1), n1P, n1P, n2z,
        fun h => hoCz (h ▸ c2), n2P, n2P⟩
    · have hb2 : 1 < So.card := by
        obtain ⟨a, ha⟩ := evz
        obtain ⟨b, hb'⟩ := evo
        obtain ⟨c, hc⟩ := hev
        omega
      obtain ⟨e1, e2, h1, h2, h12, hs⟩ := pairIn So (Or.inr fun e he => (hSo_mem e he).1) hb2
      obtain ⟨c1, n1o⟩ := hSo_mem e1 h1
      obtain ⟨c2, n2o⟩ := hSo_mem e2 h2
      exact ⟨e1, e2, h12, hs, fun h => hzCo (h ▸ c1), n1o, fun h => hPCo (h ▸ c1),
        fun h => hPCo (h ▸ c1), fun h => hzCo (h ▸ c2), n2o, fun h => hPCo (h ▸ c2),
        fun h => hPCo (h ▸ c2)⟩
  · -- `P'` in the class of `o`: `Cz` minus `z, P`, or `Co` minus `o, P'`
    have hP'Co : P' ∈ Co := by rw [hCo, mem_filter]; exact ⟨mem_univ _, hP'C⟩
    have hP'Cz : P' ∉ Cz := fun h => disjoint_left.1 hdisj h hP'Co
    set So := (Co.erase o).erase P' with hSo
    have hSoc : So.card = Co.card - 2 := by
      rw [hSo, card_erase_of_mem (mem_erase.2 ⟨hP'o, hP'Co⟩), card_erase_of_mem hoC]; omega
    have hSo_mem : ∀ e ∈ So, e ∈ Co ∧ e ≠ o ∧ e ≠ P' := by
      intro e he; simp only [hSo, mem_erase] at he; exact ⟨he.2.2, he.2.1, he.1⟩
    by_cases hb : 1 < Sz.card
    · obtain ⟨e1, e2, h1, h2, h12, hs⟩ := pairIn Sz (Or.inl fun e he => (hSz_mem e he).1) hb
      obtain ⟨c1, n1z, n1P⟩ := hSz_mem e1 h1
      obtain ⟨c2, n2z, n2P⟩ := hSz_mem e2 h2
      exact ⟨e1, e2, h12, hs, n1z, fun h => hoCz (h ▸ c1), n1P, fun h => hP'Cz (h ▸ c1), n2z,
        fun h => hoCz (h ▸ c2), n2P, fun h => hP'Cz (h ▸ c2)⟩
    · have hCo2 : 2 ≤ Co.card := by
        have := card_le_card (show ({o, P'} : Finset (Fin n)) ⊆ Co by
          intro i hi; simp only [mem_insert, mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hoC
          · exact hP'Co)
        rwa [card_pair (Ne.symm hP'o)] at this
      have hb2 : 1 < So.card := by
        obtain ⟨a, ha⟩ := evz
        obtain ⟨b, hb'⟩ := evo
        obtain ⟨c, hc⟩ := hev
        omega
      obtain ⟨e1, e2, h1, h2, h12, hs⟩ := pairIn So (Or.inr fun e he => (hSo_mem e he).1) hb2
      obtain ⟨c1, n1o, n1P'⟩ := hSo_mem e1 h1
      obtain ⟨c2, n2o, n2P'⟩ := hSo_mem e2 h2
      exact ⟨e1, e2, h12, hs, fun h => hzCo (h ▸ c1), n1o, fun h => hPCo (h ▸ c1), n1P',
        fun h => hzCo (h ▸ c2), n2o, fun h => hPCo (h ▸ c2), n2P'⟩

/-- Main Case 9 (2)(b) with exactly four odd entries: Clément's Case 3.4.
It is proved in `CaseFour.lean` (`case9_four`), which needs the joins of
`Join.lean`, and passed to the Main Lemma as a hypothesis. -/
def Case9Four (n : ℕ) : Prop :=
  ∀ {s : O n} (hs : s ≠ 1) {z o : Fin n} (hzo : z < o), (z : ℕ) = 0 → (o : ℕ) = 1 →
    sem n (Gen.H z o hzo) * s ≠ 1 → (o : ℕ) < piv s →
    lde (col s (pj s (piv_pos hs))) ≠ 0 →
    Odd (num (col s (pj s (piv_pos hs))) z).re → Odd (num (col s (pj s (piv_pos hs))) o).re →
    ¬SameOdd (num (col s (pj s (piv_pos hs))) z) (num (col s (pj s (piv_pos hs))) o) →
    (oddSet (col s (pj s (piv_pos hs)))).card = 4 → MainSquare s (Gen.H z o hzo)

/-- Main Case 9 (2)(b). -/
theorem case9_hard (four : Case9Four n) : Case9Hard n := by
  intro s hs z o hzo hz ho hr hoJ hk h0 h1 hdiff
  classical
  by_cases hl : (oddSet (col s (pj s (piv_pos hs)))).card = 4
  · exact four hs hzo hz ho hr hoJ hk h0 h1 hdiff hl
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
  obtain ⟨hlr, hnumr, hrz, hro, hrd, -⟩ := hv_odd_diff hR (ne_of_lt hzo) h0 h1 hdiff
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
  have hvP : num (hv z o v) P = num v P := hnumr P hPz hPo
  have hsame'' : SameOdd (num (hv z o v) z) (num v P') := by rw [← hvP']; exact hsame'
  have hP'cases : P' = P ∨ (P' ≠ o ∧ SameOdd (num v o) (num v P')) := by
    by_cases hc : SameOdd (num v z) (num v P')
    · left
      apply le_antisymm
      · exact hmin2' P hz1P (by rw [hvP]; exact hsame''.trans (hc.symm.trans hsame))
      · exact hmin2 P' hz2P' hc
    · right
      exact ⟨hP'o, same_of_not_not h1 hsame''.2.1 hdiff hc h0⟩
  obtain ⟨e1, e2, he, hE, h1z, h1o, h1P, h1P', h2z, h2o, h2P, h2P'⟩ :=
    exists_far_pair hR hU hk h0 h1 hdiff (Ne.symm hPz) hsame hP'cases hl
  have he2J : (e2 : ℕ) < piv s := pcol_low hp (ne_zero_of_odd hR hE.2.1)
  have hEr : SameOdd (num (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) e1)
      (num (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) e2) := by
    rw [hcolr, hnumr e1 h1z h1o, hnumr e2 h2z h2o]; exact hE
  have hA' : SameOdd (num (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) z)
      (num (col (sem n (Gen.H z o hzo) * s) (pj _ (piv_pos hr))) P') := by
    rw [hcolr]; exact hsame'
  exact case9_diamond hs hk hzo hz1P hz2P' he hr hkr hpiv hlev hsyl' hsylr' hPJ hP'J he2J hsame hE
    hA' hEr h1z h1o h1P h1P' h2z h2o h2P h2P'

end QCert.HadamardPi
