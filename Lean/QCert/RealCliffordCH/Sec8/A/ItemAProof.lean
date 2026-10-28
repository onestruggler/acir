/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (a) of the Reidemeister–Schreier theorem

For every proper letter `x` of `𝒫_N`, the coset action run on `σ(x)` from
`ε` returns to `ε` with a word equal to `x` by Figure 8 (`item_a_proof`, the
equations (DE-ZZ), (DE-ZX), (DE-XX), (DE-HH) of Appendix A.3.2).  For the
Hadamard-free letters the word is Hadamard-free with the same signed
permutation (Corollary A.5).  For `H_[a,b]H_[c,d]` the frame does it: with
tags away from `0, 1` and the indices (`exists_tags`), the word is equal to
the frame image `Φ(σ(x))` (`frame_run`), which is `H_[a,b]H_[e,f] ·
H_[c,d]H_[e,f]` up to conjugating a reversed pair by `(-1)_[g]X_[b,a]`, and
that is `H_[a,b]H_[c,d]` by Equations (66) and (71).
-/
import QCert.RealCliffordCH.Sec8.A.FrameRun

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## Tags -/

theorem exists_fresh1 (S : Finset ℕ) (hS : S.card ≤ 7) : ∃ x, x < 8 ∧ x ∉ S := by
  have h := Finset.card_le_card_sdiff_add_card (s := Finset.range 8) (t := S)
  rw [Finset.card_range] at h
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (show 0 < (Finset.range 8 \ S).card by omega)
  rw [Finset.mem_sdiff, Finset.mem_range] at hx
  exact ⟨x, hx.1, hx.2⟩

/-- Tags away from at most four indices. -/
theorem exists_tags (h8 : 8 ≤ 2 ^ n) (S : Finset ℕ) (hS : S.card ≤ 4) :
    ∃ e f g, FT n e f g ∧ e ∉ S ∧ f ∉ S ∧ g ∉ S := by
  obtain ⟨e, f, he, hf, hef, he', hf'⟩ :=
    exists_fresh_pair (S ∪ {0, 1}) ((Finset.card_union_le _ _).trans (by
      have := Finset.card_le_two (a := 0) (b := 1); omega))
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at he' hf'
  by_cases h0 : 0 ∈ S
  · obtain ⟨g, hg, hg'⟩ := exists_fresh1 (S ∪ {1, e, f}) ((Finset.card_union_le _ _).trans (by
      have := Finset.card_le_three (a := 1) (b := e) (c := f); omega))
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hg'
    refine ⟨e, f, g, ⟨by omega, by omega, by omega, hef, Ne.symm hg'.2.2.1, Ne.symm hg'.2.2.2,
      he'.2.1, he'.2.2, hf'.2.1, hf'.2.2, hg'.2.1⟩, he'.1, hf'.1, hg'.1⟩
  · refine ⟨e, f, 0, ⟨by omega, by omega, by omega, hef, he'.2.1, hf'.2.1, he'.2.1, he'.2.2,
      hf'.2.1, hf'.2.2, by norm_num⟩, he'.1, hf'.1, h0⟩

/-- Corollary A.5 for two lists of `NL` letters, decided symbolically. -/
macro "a5sym " nn:term:max L:term:max L₂:term:max : tactic =>
  `(tactic| (
    have t := a5NL (n := $nn) (L := $L) (L' := $L₂) (by omega) (by bdl) (by bdl)
      (by simp [NL.Pr] <;> omega) (by simp [NL.Pr] <;> omega) (fun j hj => by nl_eval)
    simpa [NL.toPG] using t))

end QCert.RealCliffordCH.Sec8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

theorem derivable_of_list {w : Word (PG (2 ^ n))} {x : PG (2 ^ n)} {l : List (PG (2 ^ n))}
    (h1 : w.toList = l) (h2 : D8 n l [x]) : Derivable (Fig8 n) w (FreeMonoid.of x) := by
  rw [← FreeMonoid.ofList_toList w, h1]; simpa [DR] using h2

/-! ## The Hadamard-free letters -/

set_option maxHeartbeats 1000000 in
theorem itemA_zz (h8 : 8 ≤ 2 ^ n) (a c : Fin (2 ^ n)) :
    (hstar (tauA n) Cos.e (sigmaG n (.zz a c))).2 = Cos.e ∧
      Derivable (Fig8 n) (hstar (tauA n) Cos.e (sigmaG n (.zz a c))).1 (FreeMonoid.of (.zz a c)) := by
  have ha : (a : ℕ) < 2 ^ n := a.2
  have hc : (c : ℕ) < 2 ^ n := c.2
  simp only [sigmaG, hstar_mul, hstar_of, tauA]
  refine ⟨trivial, derivable_of_list (l := [Zz n 1 a, Zz n 1 c]) (by simp [Zz, ix_fin]) ?_⟩
  have : PG.zz a c = Zz n a c := by simp [Zz, ix_fin]
  rw [this]
  a5sym n [NL.zz 1 a, NL.zz 1 c] [NL.zz a c]

set_option maxHeartbeats 1000000 in
theorem itemA_zx (h8 : 8 ≤ 2 ^ n) (a c d : Fin (2 ^ n)) (hcd : c ≠ d) :
    (hstar (tauA n) Cos.e (sigmaG n (.zx a c d))).2 = Cos.e ∧
      Derivable (Fig8 n) (hstar (tauA n) Cos.e (sigmaG n (.zx a c d))).1
        (FreeMonoid.of (.zx a c d)) := by
  have ha : (a : ℕ) < 2 ^ n := a.2
  have hc : (c : ℕ) < 2 ^ n := c.2
  have hd : (d : ℕ) < 2 ^ n := d.2
  have hcd' : (c : ℕ) ≠ d := fun e => hcd (Fin.ext e)
  have hx : PG.zx a c d = Zx n a c d := by simp [Zx, ix_fin]
  simp only [sigmaG, Xw]
  split_ifs with h1 h2
  · simp only [hstar_mul, hstar_of, tauA]
    refine ⟨trivial, derivable_of_list (l := [Zz n 1 a, Zx n 1 c d]) (by simp [Zz, Zx, ix_fin]) ?_⟩
    rw [hx]
    a5sym n [NL.zz 1 a, NL.zx 1 c d] [NL.zx a c d]
  · simp only [hstar_mul, hstar_of, tauA]
    refine ⟨trivial, derivable_of_list (l := [Zz n 1 a, Zx n 1 d c]) (by simp [Zz, Zx, ix_fin]) ?_⟩
    rw [hx]
    a5sym n [NL.zz 1 a, NL.zx 1 d c] [NL.zx a c d]
  · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) hcd

end QCert.RealCliffordCH.Sec8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

theorem swN_comm' (a b x : ℕ) : swN a b x = swN b a x := by
  unfold swN; split_ifs <;> omega

theorem xx_swap1 (hN : 4 ≤ 2 ^ n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hab : a ≠ b) (hcd : c ≠ d) :
    D8 n [Xx n a b c d] [Xx n b a c d] := by
  have := a5NL (n := n) (L := [NL.xx a b c d]) (L' := [NL.xx b a c d]) hN (by bdl) (by bdl)
    (by simp [NL.Pr]; omega) (by simp [NL.Pr]; omega)
    (fun j _ => ⟨by simp [permL, NL.perm, swN_comm'], by simp [negL, permL, NL.neg]⟩)
  simpa [NL.toPG] using this

theorem xx_swap2 (hN : 4 ≤ 2 ^ n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hab : a ≠ b) (hcd : c ≠ d) :
    D8 n [Xx n a b c d] [Xx n a b d c] := by
  have := a5NL (n := n) (L := [NL.xx a b c d]) (L' := [NL.xx a b d c]) hN (by bdl) (by bdl)
    (by simp [NL.Pr]; omega) (by simp [NL.Pr]; omega)
    (fun j _ => ⟨by simp [permL, NL.perm, swN_comm' c d], by simp [negL, permL, NL.neg]⟩)
  simpa [NL.toPG] using this

set_option maxHeartbeats 1000000 in
theorem xx_core (h8 : 8 ≤ 2 ^ n) {a b c d : ℕ} (hab : a < b) (hb : b < 2 ^ n) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) (hcd : c ≠ d) : D8 n (w2n n a b ++ [Zx n 1 c d]) [Xx n a b c d] := by
  have ha : a < 2 ^ n := by omega
  unfold w2n
  by_cases h1 : a = 1
  · subst h1
    simp only [true_or, if_true, List.singleton_append]
    a5sym n [NL.zx b 1 b, NL.zx 1 c d] [NL.xx 1 b c d]
  by_cases h2 : b = 1
  · subst h2
    have : a = 0 := by omega
    subst this
    simp only [or_true, if_true, List.singleton_append, zero_ne_one, if_false]
    a5sym n [NL.zx 0 0 1, NL.zx 1 c d] [NL.xx 0 1 c d]
  · rw [if_neg (by omega)]
    simp only [List.singleton_append]
    a5sym n [NL.zx 1 a b, NL.zx 1 c d] [NL.xx a b c d]

end QCert.RealCliffordCH.Sec8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

theorem tauZX_list (c d : Fin (2 ^ n)) (h : c < d) :
    (tauA n .z (.X c d h)).1.toList = [Zx n 1 c d] := by simp [tauA, Zx, ix_fin]

theorem Xw_lt {a b : Fin (2 ^ n)} (h : a < b) : Xw n a b = FreeMonoid.of (.X a b h) := by
  simp [Xw, h]

theorem Xw_gt {a b : Fin (2 ^ n)} (h : b < a) : Xw n a b = FreeMonoid.of (.X b a h) := by
  simp [Xw, h, not_lt.2 h.le]

theorem hstar_XX {a b c d : Fin (2 ^ n)} (h1 : a < b) (h2 : c < d) :
    hstar (tauA n) .e (FreeMonoid.of (.X a b h1) * FreeMonoid.of (.X c d h2)) =
      ((tauA n .e (.X a b h1)).1 * FreeMonoid.of (.zx (o1 n) c d), .e) := by
  rw [hstar_mul, hstar_of, hstar_of, tauA_snd]
  simp [Cos.act, gbits, tauA]

theorem itemA_xx (h8 : 8 ≤ 2 ^ n) (a b c d : Fin (2 ^ n)) (hab : a ≠ b) (hcd : c ≠ d) :
    (hstar (tauA n) Cos.e (sigmaG n (.xx a b c d))).2 = Cos.e ∧
      Derivable (Fig8 n) (hstar (tauA n) Cos.e (sigmaG n (.xx a b c d))).1
        (FreeMonoid.of (.xx a b c d)) := by
  have hN : 4 ≤ 2 ^ n := by omega
  have ha : (a : ℕ) < 2 ^ n := a.2
  have hb : (b : ℕ) < 2 ^ n := b.2
  have hc : (c : ℕ) < 2 ^ n := c.2
  have hd : (d : ℕ) < 2 ^ n := d.2
  have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
  have hcd' : (c : ℕ) ≠ d := fun e => hcd (Fin.ext e)
  have hx : PG.xx a b c d = Xx n a b c d := by simp [Xx, ix_fin]
  simp only [sigmaG]
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hcd with h2 | h2
  · rw [Xw_lt h1, Xw_lt h2, hstar_XX]
    refine ⟨rfl, derivable_of_list (l := w2n n a b ++ [Zx n 1 c d]) ?_ ?_⟩
    · rw [FreeMonoid.toList_mul, tauEX_list a b h1]; simp [Zx, ix_fin]
    · rw [hx]; exact xx_core h8 h1 hb hc hd hcd'
  · rw [Xw_lt h1, Xw_gt h2, hstar_XX]
    refine ⟨rfl, derivable_of_list (l := w2n n a b ++ [Zx n 1 d c]) ?_ ?_⟩
    · rw [FreeMonoid.toList_mul, tauEX_list a b h1]; simp [Zx, ix_fin]
    · rw [hx]; exact (xx_core h8 h1 hb hd hc (Ne.symm hcd')).trans (xx_swap2 hN ha hb hd hc hab'
        (Ne.symm hcd'))
  · rw [Xw_gt h1, Xw_lt h2, hstar_XX]
    refine ⟨rfl, derivable_of_list (l := w2n n b a ++ [Zx n 1 c d]) ?_ ?_⟩
    · rw [FreeMonoid.toList_mul, tauEX_list b a h1]; simp [Zx, ix_fin]
    · rw [hx]; exact (xx_core h8 h1 ha hc hd hcd').trans (xx_swap1 hN hb ha hc hd (Ne.symm hab')
        hcd')
  · rw [Xw_gt h1, Xw_gt h2, hstar_XX]
    refine ⟨rfl, derivable_of_list (l := w2n n b a ++ [Zx n 1 d c]) ?_ ?_⟩
    · rw [FreeMonoid.toList_mul, tauEX_list b a h1]; simp [Zx, ix_fin]
    · rw [hx]; exact ((xx_core h8 h1 ha hd hc (Ne.symm hcd')).trans (xx_swap1 hN hb ha hd hc
        (Ne.symm hab') (Ne.symm hcd'))).trans (xx_swap2 hN ha hb hd hc hab' (Ne.symm hcd'))

end QCert.RealCliffordCH.Sec8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## `H_[a,b]H_[c,d]` -/

theorem Hw_cases {a b : Fin (2 ^ n)} (hab : a ≠ b) :
    (∃ h : a < b, Hw n a b = FreeMonoid.of (.H a b h)) ∨
      (∃ h : b < a, Hw n a b = FreeMonoid.of (.X b a h) * FreeMonoid.of (.H b a h) *
        FreeMonoid.of (.X b a h)) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact Or.inl ⟨h, by simp [Hw, h]⟩
  · exact Or.inr ⟨h, by simp [Hw, h, not_lt.2 h.le]⟩

theorem Hw_par {a b : Fin (2 ^ n)} (hab : a ≠ b) (c : Cos) :
    (Hw n a b).toList.foldl (fun c y => c.act (gbits y)) c = c.act (true, false) := by
  rcases Hw_cases hab with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;> cases c <;> rfl

theorem Hw_idx {a b : Fin (2 ^ n)} (hab : a ≠ b) :
    ∀ y ∈ (Hw n a b).toList, ∀ i ∈ gix y, i = a ∨ i = b := by
  rcases Hw_cases hab with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;>
    simp [gix, FreeMonoid.toList_mul] <;> omega

theorem phiW_Hw (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : FT n e f g) {a b : Fin (2 ^ n)}
    (hab : a ≠ b) (hae : (a : ℕ) ≠ e) (haf : (a : ℕ) ≠ f) (hag : (a : ℕ) ≠ g)
    (hbe : (b : ℕ) ≠ e) (hbf : (b : ℕ) ≠ f) (hbg : (b : ℕ) ≠ g) :
    D8 n (phiW n e f g (Hw n a b)) [Hh n a b e f] := by
  have T' := T
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T'
  have ha : (a : ℕ) < 2 ^ n := a.2
  have hb : (b : ℕ) < 2 ^ n := b.2
  have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
  rcases Hw_cases hab with ⟨h, e1⟩ | ⟨h, e1⟩
  · rw [e1, phiW_of]; exact DR.refl _
  · rw [e1]
    simp only [phiW_mul, phiW_of, phiG]
    have k := push1 h8 hE (u := .zx g b a) (u' := .zx g b a) (by bd1) (by bd1)
      (by simp [NL.Pr]; omega) (by simp [NL.Pr]; omega)
      (fun v => by simpa [swN, Ne.symm hag, Ne.symm hbg] using inv_zx g b a v) hb ha he hf
      ⟨Ne.symm hab', hbe, hbf, hae, haf, hef⟩
    rw [twL_one, twL_one] at k
    simp only [NL.perm, NL.neg, swN, hab', Ne.symm hab', hae, haf, hbe, hbf, Ne.symm hae,
      Ne.symm haf, Ne.symm hbe, Ne.symm hbf, hag, hbg, heg, hfg, Ne.symm hag, Ne.symm hbg,
      Ne.symm heg, Ne.symm hfg, if_true, if_false, ite_true, ite_false, not_false_eq_true,
      List.nil_append] at k
    have c2 : D8 n [Zx n g b a, Zx n g b a] [] := by
      a5at n [b, a, g] 3 [NL.zx 2 0 1, NL.zx 2 0 1] []
    have s1 : D8 n [Zx n g b a, Hh n b a e f, Zx n g b a] [Hh n a b e f, Zx n g b a, Zx n g b a] :=
      D8.seg [] [Zx n g b a] k (by simp [NL.toPG]) (by simp [NL.toPG])
    have s2 : D8 n [Hh n a b e f, Zx n g b a, Zx n g b a] [Hh n a b e f] :=
      D8.seg [Hh n a b e f] [] c2 (by simp) (by simp)
    exact (DR.rfl' (by simp)).trans (s1.trans s2)

theorem itemA_hh (h8 : 8 ≤ 2 ^ n) (hE : E65 n) (a b c d : Fin (2 ^ n))
    (hab : a ≠ b) (hcd : c ≠ d) :
    (hstar (tauA n) Cos.e (sigmaG n (.hh a b c d))).2 = Cos.e ∧
      Derivable (Fig8 n) (hstar (tauA n) Cos.e (sigmaG n (.hh a b c d))).1
        (FreeMonoid.of (.hh a b c d)) := by
  obtain ⟨e, f, g, T, he, hf, hg⟩ :=
    exists_tags h8 ({(a : ℕ), (b : ℕ), (c : ℕ), (d : ℕ)} : Finset ℕ) Finset.card_le_four
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he hf hg
  have awayAB : Away e f g (Hw n a b) := by
    intro y hy i hi
    rcases Hw_idx hab y hy i hi with rfl | rfl
    · exact ⟨Ne.symm he.1, Ne.symm hf.1, Ne.symm hg.1⟩
    · exact ⟨Ne.symm he.2.1, Ne.symm hf.2.1, Ne.symm hg.2.1⟩
  have awayCD : Away e f g (Hw n c d) := by
    intro y hy i hi
    rcases Hw_idx hcd y hy i hi with rfl | rfl
    · exact ⟨Ne.symm he.2.2.1, Ne.symm hf.2.2.1, Ne.symm hg.2.2.1⟩
    · exact ⟨Ne.symm he.2.2.2, Ne.symm hf.2.2.2, Ne.symm hg.2.2.2⟩
  have away : Away e f g (sigmaG n (.hh a b c d)) := by
    intro y hy i hi
    simp only [sigmaG, FreeMonoid.toList_mul, List.mem_append] at hy
    exact hy.elim (fun h => awayAB y h i hi) (fun h => awayCD y h i hi)
  have hp : (hstar (tauA n) Cos.e (sigmaG n (.hh a b c d))).2 = Cos.e := by
    rw [hstar_snd]
    simp only [sigmaG, FreeMonoid.toList_mul, List.foldl_append, Hw_par hab, Hw_par hcd]
    rfl
  refine ⟨hp, ?_⟩
  have run := frame_run h8 hE T (sigmaG n (.hh a b c d)) away .e
  rw [hp] at run
  simp only [Tc, List.nil_append, List.append_nil, sigmaG, phiW_mul] at run
  have p1 := phiW_Hw h8 hE T hab (Ne.symm he.1) (Ne.symm hf.1) (Ne.symm hg.1)
    (Ne.symm he.2.1) (Ne.symm hf.2.1) (Ne.symm hg.2.1)
  have p2 := phiW_Hw h8 hE T hcd (Ne.symm he.2.2.1) (Ne.symm hf.2.2.1)
    (Ne.symm hg.2.2.1) (Ne.symm he.2.2.2) (Ne.symm hf.2.2.2) (Ne.symm hg.2.2.2)
  have merged := contract h8 hE a.2 b.2 c.2 d.2 T.he T.hf
    (fun h => hab (Fin.ext h)) ⟨fun h => hcd (Fin.ext h), Ne.symm he.2.2.1,
      Ne.symm hf.2.2.1, Ne.symm he.2.2.2, Ne.symm hf.2.2.2, T.hef⟩
  apply derivable_of_list rfl
  simpa [sigmaG, Hh, ix_fin] using run.symm.trans ((DR.append p1 p2).trans merged)

/-- Hypothesis (a), for all four kinds of proper paired generator. -/
theorem item_a_proof (n : ℕ) (hn : 3 ≤ n) : ItemA n := by
  have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  intro x hx
  cases x with
  | zz a c => exact itemA_zz h8 a c
  | zx a c d => exact itemA_zx h8 a c d hx
  | xx a b c d => exact itemA_xx h8 a b c d hx.1 hx.2
  | hh a b c d => exact itemA_hh h8 (e65 n hn) a b c d hx.1 hx.2

end QCert.RealCliffordCH.Sec8
