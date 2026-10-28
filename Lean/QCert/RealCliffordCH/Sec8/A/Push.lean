/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Conjugating a letter `H_[a,b]H_[c,d]` when the signs disagree

`hh_conj` conjugates a letter by a Hadamard-free word `P` with an inverse
when the signs of `P` agree on `a, b` and on `c, d`.  When they disagree on
`c, d` (`push_twist`), multiplying `P` by a sign pair `(-1)_[c](-1)_[x]` (`x`
away from the letter) makes them agree, at the cost of the twist of
Equation (40):

  `P · H_[a,b]H_[c,d] · P' ≈ H_[Pa,Pb]H_[Pc,Pd] · (-1)_[Pc]X_[Pd,Pc]`.

The mixed letter `(-1)_[d]X_[d,c]` conjugated by `P`, whose signs disagree on
`c, d`, is `(-1)_[Pc]X_[Pd,Pc]` (`conj_zx_flip`).
-/
import QCert.RealCliffordCH.Sec8.A.Twist

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

theorem conj_zx_flip {T T' : List NL} (hT : ∀ y ∈ T, y.Bd n) (hT' : ∀ y ∈ T', y.Bd n)
    (hinv : ∀ v < 2 ^ n, permL (T ++ T') v = v ∧ negL (T ++ T') v = false) {c d : ℕ}
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hcd : c ≠ d) (hs : negL T c = !negL T d) :
    spW (wordOf ((T ++ [NL.zx d d c] ++ T').map (NL.toPG n))) =
      spW (wordOf ([NL.zx (permL T c) (permL T d) (permL T c)].map (NL.toPG n))) := by
  have inj := permL_inj T
  have hsw : ∀ j, swN (permL T d) (permL T c) (permL T j) = permL T (swN d c j) := by
    intro j
    by_cases h1 : j = d
    · subst h1; simp [swN]
    · by_cases h2 : j = c
      · subst h2; simp [swN, inj.eq_iff, h1]
      · simp [swN, inj.eq_iff, h1, h2]
  refine conj_NL hT hT' (by simp [NL.Bd, hc, hd])
    (by simp [NL.Bd, permL_lt hT hc, permL_lt hT hd]) hinv
    (fun j _ => by simp only [permL, NL.perm, id]; exact hsw j) (fun j _ => ?_)
  simp only [negL, permL, id, NL.neg, NL.perm, hsw, inj.eq_iff]
  by_cases h1 : j = d
  · subst h1; simp [swN, hcd, Ne.symm hcd, hs]
  · by_cases h2 : j = c
    · subst h2; simp [swN, h1, hs, hcd, Ne.symm hcd]
    · simp [swN, h1, h2]

/-- Conjugating a letter by a word whose signs disagree on its second pair. -/
theorem push_twist (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {P P' : List NL} (hbd : ∀ y ∈ P, y.Bd n)
    (hbd' : ∀ y ∈ P', y.Bd n) (hpr : ∀ y ∈ P, y.Pr) (hpr' : ∀ y ∈ P', y.Pr)
    (hinv : ∀ v < 2 ^ n, permL (P ++ P') v = v ∧ negL (P ++ P') v = false) {a b c d x : ℕ}
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hx : x < 2 ^ n)
    (h : Distinct4 a b c d) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d)
    (s1 : negL P a = negL P b) (s2 : negL P c = !negL P d) :
    D8 n (P.map (NL.toPG n) ++ Hh n a b c d :: P'.map (NL.toPG n))
      [Hh n (permL P a) (permL P b) (permL P c) (permL P d),
        Zx n (permL P c) (permL P d) (permL P c)] := by
  have hN : 4 ≤ 2 ^ n := by omega
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h
  have bz : ∀ y ∈ [NL.zz c x], y.Bd n := by
    intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact ⟨hc, hx⟩
  have pz : ∀ y ∈ [NL.zz c x], y.Pr := by
    intro y hy; simp only [List.mem_singleton] at hy; subst hy; trivial
  -- `Q = P (-1)_[c](-1)_[x]` and its inverse
  have hQinv : ∀ v < 2 ^ n, permL ((P ++ [NL.zz c x]) ++ ([NL.zz c x] ++ P')) v = v ∧
      negL ((P ++ [NL.zz c x]) ++ ([NL.zz c x] ++ P')) v = false := by
    intro v hv
    have e1 : (P ++ [NL.zz c x]) ++ ([NL.zz c x] ++ P') = P ++ ([NL.zz c x, NL.zz c x] ++ P') := by
      simp
    have hp : ∀ w, permL ([NL.zz c x, NL.zz c x] ++ P') w = permL P' w := fun w => by
      rw [permL_append, (NL.inv_zz c x _).1]
    have hn : ∀ w, negL ([NL.zz c x, NL.zz c x] ++ P') w = negL P' w := fun w => by
      rw [negL_append, (NL.inv_zz c x _).2]; exact Bool.false_xor _
    rw [e1]
    refine ⟨?_, ?_⟩
    · rw [permL_append, hp, ← permL_append]; exact (hinv v hv).1
    · rw [negL_append, hp, hn, ← negL_append]; exact (hinv v hv).2
  have hQp : ∀ j, permL (P ++ [NL.zz c x]) j = permL P j := fun j => by
    rw [permL_append]; rfl
  have hQn : ∀ j, negL (P ++ [NL.zz c x]) j = xor (negL P j) (NL.neg (NL.zz c x) j) := fun j => by
    rw [negL_append]; simp [negL, permL, NL.perm]
  have qs1 : negL (P ++ [NL.zz c x]) a = negL (P ++ [NL.zz c x]) b := by
    rw [hQn, hQn]; simp [NL.neg, d2, Ne.symm hxa, d4, Ne.symm hxb, s1]
  have qs2 : negL (P ++ [NL.zz c x]) c = negL (P ++ [NL.zz c x]) d := by
    rw [hQn, hQn]; simp [NL.neg, Ne.symm hxc, Ne.symm d6, Ne.symm hxd, s2]
  have k1 := hh_conj h8 hE (P := P ++ [NL.zz c x]) (P' := [NL.zz c x] ++ P')
    (fun y hy => (List.mem_append.1 hy).elim (hbd y) (bz y))
    (fun y hy => (List.mem_append.1 hy).elim (bz y) (hbd' y))
    (fun y hy => (List.mem_append.1 hy).elim (hpr y) (pz y))
    (fun y hy => (List.mem_append.1 hy).elim (pz y) (hpr' y)) hQinv ha hb hc hd
    ⟨d1, d2, d3, d4, d5, d6⟩ qs1 qs2
  rw [hQp, hQp, hQp, hQp] at k1
  have hHP := HP_NL hbd hpr
  have hHP' := HP_NL hbd' hpr'
  have hzx : ∀ y ∈ [NL.zx d d c], y.Bd n := by
    intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact ⟨hd, hd, hc⟩
  have pzx : ∀ y ∈ [NL.zx d d c], y.Pr := by
    intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact Ne.symm d6
  have k2 : D8 n (P.map (NL.toPG n) ++ [Zx n d d c] ++ P'.map (NL.toPG n))
      [Zx n (permL P c) (permL P d) (permL P c)] := by
    have e := conj_zx_flip hbd hbd' hinv hc hd d6 s2
    have hz2 : ∀ y ∈ [NL.zx (permL P c) (permL P d) (permL P c)], y.Bd n := by
      intro y hy; simp only [List.mem_singleton] at hy; subst hy
      exact ⟨permL_lt hbd hc, permL_lt hbd hd, permL_lt hbd hc⟩
    have pz2 : ∀ y ∈ [NL.zx (permL P c) (permL P d) (permL P c)], y.Pr := by
      intro y hy; simp only [List.mem_singleton] at hy; subst hy
      exact fun e' => d6 (permL_inj P e'.symm)
    refine A5s hN ?_ (HP_NL hz2 pz2) ?_
    · exact (hHP.append (HP_NL hzx pzx)).append hHP'
    · simpa only [List.map_append, List.map_cons, List.map_nil, NL.toPG] using e
  have c0 : D8 n [] (P'.map (NL.toPG n) ++ P.map (NL.toPG n)) := by
    refine A5s hN HP.nil (hHP'.append hHP) ?_
    rw [spW_nil, inv_comm]
    rw [← List.map_append]
    exact spW_one_NL (fun y hy => (List.mem_append.1 hy).elim (hbd y) (hbd' y)) hinv
  have tw := twist h8 hE ha hb hc hd hx ⟨d1, d2, d3, d4, d5, d6⟩ hxa hxb hxc hxd
  have zsq : D8 n [] [Zz n c x, Zz n c x] := (DH.toD8 (zz_sq hc hx)).symm
  set A := P.map (NL.toPG n)
  set A' := P'.map (NL.toPG n)
  refine (DR.rfl' (by simp)).trans ((DR.ctx A (Hh n a b c d :: A') zsq).trans ?_)
  refine (DR.rfl' (by simp)).trans ((DR.ctx (A ++ [Zz n c x]) A' tw).trans ?_)
  refine (DR.rfl' (by simp)).trans ((DR.ctx (A ++ [Zz n c x, Hh n a b c d, Zz n c x])
    ([Zx n d d c] ++ A') c0).trans ?_)
  refine (DR.rfl' ?_).trans (DR.append k1 k2)
  simp [A, A', NL.toPG]

end QCert.RealCliffordCH.Sec8
