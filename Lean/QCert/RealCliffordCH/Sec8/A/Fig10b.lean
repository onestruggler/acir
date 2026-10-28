/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Figure 10, continued: Equation (71) in general, conjugation of a letter

* A letter `H_[a,b]H_[c,d]` (four distinct indices) squared is `ε` (`hh_sq`).
* Splitting through a fresh pair (`hh_split`): `H_[x,y]H_[z,w] ≈
  H_[x,y]H_[p,q] · H_[p,q]H_[z,w]` for every pair `p, q` away from `x, y, z, w`,
  whether or not `x, y, z, w` are distinct — Equation (71) for six distinct
  indices when they are, and otherwise Equation (42), which splits through
  its own fresh pair, moved to `p, q` through (71) (`hh_move`), via a third
  pair when the two overlap.  With `N = 2ⁿ ≥ 8` there is always room.
* Equation (71) for any indices (`e71`).
* A proper Hadamard-free word `P` with an inverse `P'` conjugates
  `H_[a,b]H_[c,d]` into the letter on the images of `a, b, c, d` when its signs
  on `a, b` agree and on `c, d` agree (`hh_conj`): the conjugate of a frame is
  a frame.
-/
import QCert.RealCliffordCH.Sec8.A.Fig10

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## Fresh pairs -/

theorem exists_fresh_pair (S : Finset ℕ) (hS : S.card ≤ 6) :
    ∃ r s, r < 8 ∧ s < 8 ∧ r ≠ s ∧ r ∉ S ∧ s ∉ S := by
  have h := Finset.card_le_card_sdiff_add_card (s := Finset.range 8) (t := S)
  rw [Finset.card_range] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (show 1 < (Finset.range 8 \ S).card by omega)
  rw [Finset.mem_sdiff, Finset.mem_range] at hx hy
  exact ⟨x, y, hx.1, hy.1, hxy, hx.2, hy.2⟩

theorem card4_le3 {x y z w : ℕ} (h : ¬ Distinct4 x y z w) :
    ({x, y, z, w} : Finset ℕ).card ≤ 3 := by
  have key : ∀ u v t : ℕ, (∀ s, s = x ∨ s = y ∨ s = z ∨ s = w → s = u ∨ s = v ∨ s = t) →
      ({x, y, z, w} : Finset ℕ).card ≤ 3 := fun u v t hs =>
    (Finset.card_le_card (fun s hs' => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs' ⊢; exact hs s hs')).trans
      Finset.card_le_three
  unfold Distinct4 at h
  by_cases h1 : x = y
  · exact key y z w fun s hs => by omega
  by_cases h2 : x = z
  · exact key y z w fun s hs => by omega
  by_cases h3 : x = w
  · exact key y z w fun s hs => by omega
  by_cases h4 : y = z
  · exact key x z w fun s hs => by omega
  by_cases h5 : y = w
  · exact key x z w fun s hs => by omega
  by_cases h6 : z = w
  · exact key x y w fun s hs => by omega
  exact absurd ⟨h1, h2, h3, h4, h5, h6⟩ h

theorem nodup6 {a b c d e f : ℕ} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : a ≠ e)
    (h5 : a ≠ f) (h6 : b ≠ c) (h7 : b ≠ d) (h8 : b ≠ e) (h9 : b ≠ f) (h10 : c ≠ d)
    (h11 : c ≠ e) (h12 : c ≠ f) (h13 : d ≠ e) (h14 : d ≠ f) (h15 : e ≠ f) :
    [a, b, c, d, e, f].Nodup := by
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

/-! ## A letter squared, and splitting through a fresh pair -/

/-- `H_[a,b]H_[c,d] · H_[a,b]H_[c,d] ≈ ε` for four distinct indices. -/
theorem hh_sq (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (h : Distinct4 a b c d) :
    D8 n [Hh n a b c d, Hh n a b c d] [] := by
  have F := Frame.sigma h8 ha hb hc hd h
  have h1 := hh_frame h8 hE ha hb hc hd h F
  obtain ⟨c1, c2⟩ := frame_cancel (by omega) F
  set A := (sigmaW n a b c d).1
  set A' := (sigmaW n a b c d).2
  refine (DR.append h1 h1).trans ?_
  refine (DR.rfl' (by simp)).trans ((DR.ctx (A ++ [Lam n]) (Lam n :: A') c1).trans ?_)
  refine (DR.rfl' (by simp)).trans ((DR.ctx A A' e41).trans ?_)
  exact (DR.rfl' (by simp)).trans c2

/-- Moving the middle pair: `H_[x,y]H_[p,q] · H_[p,q]H_[z,w] ≈ H_[x,y]H_[p',q'] · H_[p',q']H_[z,w]`
for disjoint pairs `p, q` and `p', q'` away from `x, y, z, w`. -/
theorem hh_move (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {x y z w p q p' q' : ℕ} (hx : x < 2 ^ n)
    (hy : y < 2 ^ n) (hz : z < 2 ^ n) (hw : w < 2 ^ n) (hp : p < 2 ^ n) (hq : q < 2 ^ n)
    (hp' : p' < 2 ^ n) (hq' : q' < 2 ^ n) (hxy : x ≠ y) (hzw : z ≠ w) (hpq : p ≠ q)
    (hpq' : p' ≠ q') (fp : p ≠ x ∧ p ≠ y ∧ p ≠ z ∧ p ≠ w) (fq : q ≠ x ∧ q ≠ y ∧ q ≠ z ∧ q ≠ w)
    (fp' : p' ≠ x ∧ p' ≠ y ∧ p' ≠ z ∧ p' ≠ w) (fq' : q' ≠ x ∧ q' ≠ y ∧ q' ≠ z ∧ q' ≠ w)
    (hdis : Distinct4 p q p' q') :
    D8 n [Hh n x y p q, Hh n p q z w] [Hh n x y p' q', Hh n p' q' z w] := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hdis
  have k1 := e71_distinct (n := n) h8 hE hx hy hp' hq' hp hq
    (nodup6 hxy (Ne.symm fp'.1) (Ne.symm fq'.1) (Ne.symm fp.1) (Ne.symm fq.1) (Ne.symm fp'.2.1)
      (Ne.symm fq'.2.1) (Ne.symm fp.2.1) (Ne.symm fq.2.1) hpq' (Ne.symm d2) (Ne.symm d4)
      (Ne.symm d3) (Ne.symm d5) hpq)
  have k2 := e71_distinct (n := n) h8 hE hp' hq' hp hq hz hw
    (nodup6 hpq' (Ne.symm d2) (Ne.symm d4) fp'.2.2.1 fp'.2.2.2 (Ne.symm d3) (Ne.symm d5)
      fq'.2.2.1 fq'.2.2.2 hpq fp.2.2.1 fp.2.2.2 fq.2.2.1 fq.2.2.2 hzw)
  exact (DR.right [Hh n p q z w] k1.symm).trans (DR.left [Hh n x y p' q'] k2)

/-- Splitting a letter through a pair away from its indices. -/
theorem hh_split (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {x y z w p q : ℕ} (hx : x < 2 ^ n)
    (hy : y < 2 ^ n) (hz : z < 2 ^ n) (hw : w < 2 ^ n) (hp : p < 2 ^ n) (hq : q < 2 ^ n)
    (hxy : x ≠ y) (hzw : z ≠ w) (hpq : p ≠ q) (fp : p ≠ x ∧ p ≠ y ∧ p ≠ z ∧ p ≠ w)
    (fq : q ≠ x ∧ q ≠ y ∧ q ≠ z ∧ q ≠ w) :
    D8 n [Hh n x y z w] [Hh n x y p q, Hh n p q z w] := by
  by_cases hd : Distinct4 x y z w
  · obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
    exact (e71_distinct (n := n) h8 hE hx hy hp hq hz hw
      (nodup6 hxy (Ne.symm fp.1) (Ne.symm fq.1) d2 d3 (Ne.symm fp.2.1) (Ne.symm fq.2.1) d4 d5
        hpq fp.2.2.1 fp.2.2.2 fq.2.2.1 fq.2.2.2 hzw)).symm
  obtain ⟨g, h, hgh, hg, hh, hgh', fg, fh⟩ := freshPair_spec (n := n) (by omega) x y z w
  have h42 : D8 n [Hh n x y g h, Hh n g h z w] [Hh n x y z w] := by
    have := DR.ax (Γ := Fig8 n) (Fig8.r42 x y z w hx hy hz hw hxy hzw hd)
    simpa only [hgh] using this
  refine h42.symm.trans ?_
  by_cases hd2 : Distinct4 g h p q
  · exact hh_move h8 hE hx hy hz hw hg hh hp hq hxy hzw hgh' hpq fg fh fp fq hd2
  · -- through a third pair
    have hc : (({x, y, z, w} : Finset ℕ) ∪ {g, h, p, q}).card ≤ 6 :=
      (Finset.card_union_le _ _).trans (by have := card4_le3 hd; have := card4_le3 hd2; omega)
    obtain ⟨r, s, hr, hs, hrs, hr', hs'⟩ := exists_fresh_pair _ hc
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hr' hs'
    have m1 := hh_move h8 hE hx hy hz hw hg hh (show r < 2 ^ n by omega) (show s < 2 ^ n by omega)
      hxy hzw hgh' hrs fg fh ⟨hr'.1.1, hr'.1.2.1, hr'.1.2.2.1, hr'.1.2.2.2⟩
      ⟨hs'.1.1, hs'.1.2.1, hs'.1.2.2.1, hs'.1.2.2.2⟩
      ⟨hgh', Ne.symm hr'.2.1, Ne.symm hs'.2.1, Ne.symm hr'.2.2.1, Ne.symm hs'.2.2.1, hrs⟩
    have m2 := hh_move h8 hE hx hy hz hw (show r < 2 ^ n by omega) (show s < 2 ^ n by omega) hp hq
      hxy hzw hrs hpq ⟨hr'.1.1, hr'.1.2.1, hr'.1.2.2.1, hr'.1.2.2.2⟩
      ⟨hs'.1.1, hs'.1.2.1, hs'.1.2.2.1, hs'.1.2.2.2⟩ fp fq
      ⟨hrs, hr'.2.2.2.1, hr'.2.2.2.2, hs'.2.2.2.1, hs'.2.2.2.2, hpq⟩
    exact m1.trans m2

/-- **Equation (71)**: `H_[a,b]H_[c,d] · H_[c,d]H_[e,f] ≈ H_[a,b]H_[e,f]`. -/
theorem e71 (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d e f : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (he : e < 2 ^ n) (hf : f < 2 ^ n) (hab : a ≠ b)
    (hcd : c ≠ d) (hef : e ≠ f) :
    D8 n [Hh n a b c d, Hh n c d e f] [Hh n a b e f] := by
  obtain ⟨p, q, hp, hq, hpq, hp', hq'⟩ :=
    exists_fresh_pair ({a, b, c, d, e, f} : Finset ℕ) Finset.card_le_six
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp' hq'
  obtain ⟨pa, pb, pc, pd, pe, pf⟩ := hp'
  obtain ⟨qa, qb, qc, qd, qe, qf⟩ := hq'
  have hp2 : p < 2 ^ n := by omega
  have hq2 : q < 2 ^ n := by omega
  have s1 := hh_split h8 hE ha hb hc hd hp2 hq2 hab hcd hpq ⟨pa, pb, pc, pd⟩ ⟨qa, qb, qc, qd⟩
  have s2 := hh_split h8 hE hc hd he hf hp2 hq2 hcd hef hpq ⟨pc, pd, pe, pf⟩ ⟨qc, qd, qe, qf⟩
  have s3 := hh_split h8 hE ha hb he hf hp2 hq2 hab hef hpq ⟨pa, pb, pe, pf⟩ ⟨qa, qb, qe, qf⟩
  have hdist : Distinct4 c d p q := ⟨hcd, Ne.symm pc, Ne.symm qc, Ne.symm pd, Ne.symm qd, hpq⟩
  have m1 := e66 h8 hE hc hd hp2 hq2 hdist
  have m2 := hh_sq h8 hE hp2 hq2 hc hd hdist.swap
  have mid : D8 n [Hh n p q c d, Hh n c d p q] [] := (DR.left [Hh n p q c d] m1).trans m2
  refine (DR.append s1 s2).trans ?_
  refine (DR.rfl' (by simp)).trans ((DR.ctx [Hh n a b p q] [Hh n p q e f] mid).trans ?_)
  exact (DR.rfl' (by simp)).trans s3.symm

/-! ## Conjugating a letter by a Hadamard-free word -/

theorem NL.perm_inj (x : NL) : Function.Injective x.perm := by
  cases x with
  | zz _ _ => exact fun _ _ h => h
  | zx a c d => exact swN_inj c d
  | xx a b c d => exact (swN_inj a b).comp (swN_inj c d)

theorem permL_inj : ∀ l : List NL, Function.Injective (permL l)
  | [] => fun _ _ h => h
  | x :: l => fun u v h => permL_inj l (NL.perm_inj x h)

theorem permL_lt {l : List NL} (hl : ∀ x ∈ l, x.Bd n) {v : ℕ} (hv : v < 2 ^ n) :
    permL l v < 2 ^ n := by
  induction l with
  | nil => exact hv
  | cons x l ih =>
    exact perm_lt (hl x (by simp)) (ih fun y hy => hl y (List.mem_cons_of_mem _ hy))

/-- A proper Hadamard-free word with an inverse conjugates `H_[a,b]H_[c,d]` into
the letter on the images, when its signs agree on `a, b` and on `c, d`. -/
theorem hh_conj (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {P P' : List NL} (hbd : ∀ y ∈ P, y.Bd n)
    (hbd' : ∀ y ∈ P', y.Bd n) (hpr : ∀ y ∈ P, y.Pr) (hpr' : ∀ y ∈ P', y.Pr)
    (hinv : ∀ v < 2 ^ n, permL (P ++ P') v = v ∧ negL (P ++ P') v = false) {a b c d : ℕ}
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n) (h : Distinct4 a b c d)
    (s1 : negL P a = negL P b) (s2 : negL P c = negL P d) :
    D8 n (P.map (NL.toPG n) ++ Hh n a b c d :: P'.map (NL.toPG n))
      [Hh n (permL P a) (permL P b) (permL P c) (permL P d)] := by
  have F := Frame.sigma h8 ha hb hc hd h
  have G := Frame.conjNL F ha hb hc hd hbd hbd' hpr hpr' hinv s1 s2
  have inj := permL_inj P
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h
  have hG : Distinct4 (permL P a) (permL P b) (permL P c) (permL P d) :=
    ⟨fun e => d1 (inj e), fun e => d2 (inj e), fun e => d3 (inj e), fun e => d4 (inj e),
      fun e => d5 (inj e), fun e => d6 (inj e)⟩
  have k := hh_frame h8 hE (permL_lt hbd ha) (permL_lt hbd hb) (permL_lt hbd hc)
    (permL_lt hbd hd) hG G
  have k0 := hE a b c d ha hb hc hd ⟨d1, d2, d3, d4, d5, d6⟩
  refine (DR.rfl' (by simp)).trans ((DR.ctx (P.map (NL.toPG n)) (P'.map (NL.toPG n)) k0).trans ?_)
  exact (DR.rfl' (by simp)).trans k.symm

end QCert.RealCliffordCH.Sec8
