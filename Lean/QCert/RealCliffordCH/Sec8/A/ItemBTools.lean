/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Toward hypothesis (b): conjugating a letter by any Hadamard-free word

* `A5NL`: Corollary A.5 for lists of `NL` letters, from the pointwise
  equality of their signed permutations.
* `conj_hh`: a Hadamard-free word `P` with an inverse `P'` conjugates
  `H_[a,b]H_[c,d]` (four distinct indices) into the letter on the images,
  followed by `(-1)_[Pa]X_[Pa,Pb]` when the signs of `P` disagree on `a, b`,
  and by `(-1)_[Pc]X_[Pc,Pd]` when they disagree on `c, d`.  The four cases are
  `hh_conj` (both agree), `push_twist` (the second pair disagrees), the same
  after Equation (66) (the first pair disagrees), and, when both disagree, the
  last case through a sign pair `(-1)_[a](-1)_[x]` with `x` fresh, which flips
  the sign of `a`.
* `push_hh`: the same with the conjugating word moved to the right.
-/
import QCert.RealCliffordCH.Sec8.A.Push

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- Corollary A.5 for lists of `NL` letters. -/
theorem A5NL (hN : 4 ≤ 2 ^ n) {l l' : List NL} (hb : ∀ x ∈ l, x.Bd n) (hb' : ∀ x ∈ l', x.Bd n)
    (hp : ∀ x ∈ l, x.Pr) (hp' : ∀ x ∈ l', x.Pr)
    (h : ∀ j < 2 ^ n, permL l j = permL l' j ∧ negL l j = negL l' j) :
    D8 n (l.map (NL.toPG n)) (l'.map (NL.toPG n)) :=
  A5s hN (HP_NL hb hp) (HP_NL hb' hp') (spW_eq_of_NL hb hb' h)

theorem Distinct4.map {a b c d : ℕ} (h : Distinct4 a b c d) {f : ℕ → ℕ}
    (hf : Function.Injective f) : Distinct4 (f a) (f b) (f c) (f d) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h
  exact ⟨fun e => d1 (hf e), fun e => d2 (hf e), fun e => d3 (hf e), fun e => d4 (hf e),
    fun e => d5 (hf e), fun e => d6 (hf e)⟩

/-- The twist of a pair: `(-1)_[Pa]X_[Pa,Pb]` when the signs of `P` disagree on `a, b`. -/
def twL (n : ℕ) (P : List NL) (a b : ℕ) : List (PG (2 ^ n)) :=
  if negL P a = negL P b then [] else [Zx n (permL P a) (permL P b) (permL P a)]

theorem twL_agree {P : List NL} {a b : ℕ} (h : negL P a = negL P b) : twL n P a b = [] := by
  simp [twL, h]

theorem twL_disagree {P : List NL} {a b : ℕ} (h : negL P a = !negL P b) :
    twL n P a b = [Zx n (permL P a) (permL P b) (permL P a)] := by
  simp [twL, h]

theorem bool_ne {x y : Bool} (h : ¬ x = y) : x = !y := by
  cases x <;> cases y <;> simp_all

/-- A single proper `(-1)_[u]X_[v,w]`. -/
theorem HP_zx {u v w : ℕ} (hu : u < 2 ^ n) (hv : v < 2 ^ n) (hw : w < 2 ^ n) (hvw : v ≠ w) :
    HP [Zx n u v w] := by
  intro y hy; simp only [List.mem_singleton] at hy; subst hy
  refine ⟨trivial, fun e => hvw ?_⟩
  have := congrArg Fin.val e; rwa [ix_val hv, ix_val hw] at this

theorem HP_zz (u v : ℕ) : HP [Zz n u v] := by
  intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact ⟨trivial, trivial⟩

/-- A Hadamard-free word and its inverse cancel, in both orders. -/
theorem cancel_NL (hN : 4 ≤ 2 ^ n) {T T' : List NL} (hbd : ∀ y ∈ T, y.Bd n)
    (hbd' : ∀ y ∈ T', y.Bd n) (hpr : ∀ y ∈ T, y.Pr) (hpr' : ∀ y ∈ T', y.Pr)
    (hinv : ∀ v < 2 ^ n, permL (T ++ T') v = v ∧ negL (T ++ T') v = false) :
    D8 n (T.map (NL.toPG n) ++ T'.map (NL.toPG n)) [] ∧
      D8 n (T'.map (NL.toPG n) ++ T.map (NL.toPG n)) [] := by
  have h1 : spW (wordOf (T.map (NL.toPG n) ++ T'.map (NL.toPG n))) = 1 := by
    rw [← List.map_append]
    exact spW_one_NL (fun x hx => (List.mem_append.1 hx).elim (hbd x) (hbd' x)) hinv
  exact ⟨A5s hN ((HP_NL hbd hpr).append (HP_NL hbd' hpr')) HP.nil (by rw [h1, spW_nil]),
    A5s hN ((HP_NL hbd' hpr').append (HP_NL hbd hpr)) HP.nil (by rw [inv_comm h1, spW_nil])⟩

/-! ## Conjugation, case by case -/

section Conj

variable (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {P P' : List NL} (hbd : ∀ y ∈ P, y.Bd n)
  (hbd' : ∀ y ∈ P', y.Bd n) (hpr : ∀ y ∈ P, y.Pr) (hpr' : ∀ y ∈ P', y.Pr)
  (hinv : ∀ v < 2 ^ n, permL (P ++ P') v = v ∧ negL (P ++ P') v = false)
  {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
  (h : Distinct4 a b c d)
include h8 hE hbd hbd' hpr hpr' hinv ha hb hc hd h

/-- The first pair disagrees, the second agrees. -/
theorem conj_DA (s1 : negL P a = !negL P b) (s2 : negL P c = negL P d) :
    D8 n (P.map (NL.toPG n) ++ Hh n a b c d :: P'.map (NL.toPG n))
      [Hh n (permL P a) (permL P b) (permL P c) (permL P d),
        Zx n (permL P a) (permL P b) (permL P a)] := by
  obtain ⟨x, _y, hx6, -, -, ⟨hxa, hxb, hxc, hxd⟩, -⟩ := two_fresh a b c d
  have k := push_twist h8 hE hbd hbd' hpr hpr' hinv hc hd ha hb (by omega : x < 2 ^ n) h.swap
    hxc hxd hxa hxb s2 s1
  have hs := h.swap.map (permL_inj P)
  refine (DR.rfl' (by simp)).trans ((DR.ctx (P.map (NL.toPG n)) (P'.map (NL.toPG n))
    (e66 h8 hE ha hb hc hd h)).trans ?_)
  refine (DR.rfl' (by simp)).trans (k.trans ?_)
  exact DR.right _ (e66 h8 hE (permL_lt hbd hc) (permL_lt hbd hd) (permL_lt hbd ha)
    (permL_lt hbd hb) hs)

/-- Both pairs disagree. -/
theorem conj_DD (s1 : negL P a = !negL P b) (s2 : negL P c = !negL P d) :
    D8 n (P.map (NL.toPG n) ++ Hh n a b c d :: P'.map (NL.toPG n))
      [Hh n (permL P a) (permL P b) (permL P c) (permL P d),
        Zx n (permL P c) (permL P d) (permL P c), Zx n (permL P a) (permL P b) (permL P a)] := by
  have hN : 4 ≤ 2 ^ n := by omega
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h
  obtain ⟨x, _y, hx6, -, -, ⟨hxa, hxb, hxc, hxd⟩, -⟩ := two_fresh a b c d
  have hx : x < 2 ^ n := by omega
  set Q := P ++ [NL.zz a x]
  set Q' := [NL.zz a x] ++ P'
  have bz : ∀ y ∈ [NL.zz a x], y.Bd n := by simp [NL.Bd, ha, hx]
  have pz : ∀ y ∈ [NL.zz a x], y.Pr := by simp [NL.Pr]
  have hbQ : ∀ y ∈ Q, y.Bd n := fun y hy => (List.mem_append.1 hy).elim (hbd y) (bz y)
  have hbQ' : ∀ y ∈ Q', y.Bd n := fun y hy => (List.mem_append.1 hy).elim (bz y) (hbd' y)
  have hpQ : ∀ y ∈ Q, y.Pr := fun y hy => (List.mem_append.1 hy).elim (hpr y) (pz y)
  have hpQ' : ∀ y ∈ Q', y.Pr := fun y hy => (List.mem_append.1 hy).elim (pz y) (hpr' y)
  have hpermQ : ∀ j, permL Q j = permL P j := fun j => by
    simp only [Q, permL_append]; rfl
  have zn : ∀ j, (NL.zz a x).neg j = (decide (j = a) ^^ decide (j = x)) := fun j => by
    simp only [NL.neg]; by_cases h1 : j = a <;> by_cases h2 : j = x <;> simp [h1, h2]
  have hnegQ : ∀ j, negL Q j = (negL P j ^^ (decide (j = a) ^^ decide (j = x))) := fun j => by
    rw [negL_append, ← zn]
    cases hz : (NL.zz a x).neg j <;> simp [negL, permL, NL.perm, hz]
  have hinvQ : ∀ v < 2 ^ n, permL (Q ++ Q') v = v ∧ negL (Q ++ Q') v = false := by
    intro v hv
    have e1 : Q ++ Q' = P ++ ([NL.zz a x, NL.zz a x] ++ P') := by simp [Q, Q']
    have hp : ∀ w, permL ([NL.zz a x, NL.zz a x] ++ P') w = permL P' w := fun w => by
      rw [permL_append, (NL.inv_zz a x _).1]
    have hn : ∀ w, negL ([NL.zz a x, NL.zz a x] ++ P') w = negL P' w := fun w => by
      rw [negL_append, (NL.inv_zz a x _).2]; exact Bool.false_xor _
    rw [e1]
    refine ⟨?_, ?_⟩
    · rw [permL_append, hp, ← permL_append]; exact (hinv v hv).1
    · rw [negL_append, hp, hn, ← negL_append]; exact (hinv v hv).2
  have qa : negL Q a = negL Q b := by
    rw [hnegQ, hnegQ, s1]; simp [Ne.symm hxa, Ne.symm d1, Ne.symm hxb]
  have qc : negL Q c = !negL Q d := by
    rw [hnegQ, hnegQ, s2]
    simp [Ne.symm d2, Ne.symm d3, Ne.symm hxc, Ne.symm hxd]
  -- insert the sign pair twice
  have zz2 := (zz_sq (n := n) ha hx).toD8
  have step1 : D8 n (P.map (NL.toPG n) ++ Hh n a b c d :: P'.map (NL.toPG n))
      (Q.map (NL.toPG n) ++ [Zz n a x, Hh n a b c d, Zz n a x] ++ Q'.map (NL.toPG n)) := by
    have k1 := DR.ctx (P.map (NL.toPG n)) (Hh n a b c d :: P'.map (NL.toPG n)) zz2
    have k2 := DR.ctx (P.map (NL.toPG n) ++ [Zz n a x, Zz n a x, Hh n a b c d])
      (P'.map (NL.toPG n)) zz2
    refine (DR.rfl' (by simp)).trans (k1.symm.trans ((DR.rfl' (by simp)).trans
      (k2.symm.trans (DR.rfl' (by simp [Q, Q', NL.toPG])))))
  -- the inner conjugation by the sign pair
  have inner : D8 n [Zz n a x, Hh n a b c d, Zz n a x] [Hh n a b c d, Zx n a b a] := by
    have k := conj_DA h8 hE bz bz pz pz (fun v _ => NL.inv_zz a x v) ha hb hc hd
      ⟨d1, d2, d3, d4, d5, d6⟩
      (by simp [negL, permL, NL.neg, Ne.symm hxa, Ne.symm d1, Ne.symm hxb])
      (by simp [negL, permL, NL.neg, Ne.symm d2, Ne.symm d3, Ne.symm hxc, Ne.symm hxd])
    simpa [permL, NL.perm, NL.toPG] using k
  obtain ⟨-, cQ⟩ := cancel_NL hN hbQ hbQ' hpQ hpQ' hinvQ
  have kAD := push_twist h8 hE hbQ hbQ' hpQ hpQ' hinvQ ha hb hc hd hx ⟨d1, d2, d3, d4, d5, d6⟩
    hxa hxb hxc hxd qa qc
  have hzx : spW (wordOf ((Q ++ [NL.zx a b a] ++ Q').map (NL.toPG n))) =
      spW (wordOf ([NL.zx (permL Q a) (permL Q b) (permL Q a)].map (NL.toPG n))) :=
    conj_zx hbQ hbQ' hinvQ ha hb ha qa.symm
  have kzx : D8 n (Q.map (NL.toPG n) ++ Zx n a b a :: Q'.map (NL.toPG n))
      [Zx n (permL P a) (permL P b) (permL P a)] := by
    have hm := (HP_NL hbQ hpQ).append ((HP_zx (n := n) ha hb ha (Ne.symm d1)).append (HP_NL hbQ' hpQ'))
    refine A5s hN (by simpa using hm)
      (HP_zx (permL_lt hbd ha) (permL_lt hbd hb) (permL_lt hbd ha)
        (fun e => d1 (permL_inj P e).symm)) ?_
    rw [← hpermQ, ← hpermQ]
    simpa [NL.toPG] using hzx
  refine step1.trans ((DR.ctx _ _ inner).trans ?_)
  -- split the conjugation over the two letters
  have split : D8 n (Q.map (NL.toPG n) ++ [Hh n a b c d, Zx n a b a] ++ Q'.map (NL.toPG n))
      ((Q.map (NL.toPG n) ++ Hh n a b c d :: Q'.map (NL.toPG n)) ++
        (Q.map (NL.toPG n) ++ Zx n a b a :: Q'.map (NL.toPG n))) := by
    have k3 := DR.ctx (Q.map (NL.toPG n) ++ [Hh n a b c d]) (Zx n a b a :: Q'.map (NL.toPG n)) cQ
    exact (DR.rfl' (by simp)).trans (k3.symm.trans (DR.rfl' (by simp)))
  refine split.trans ((DR.append kAD kzx).trans (DR.rfl' ?_))
  simp [hpermQ]

/-- Conjugating `H_[a,b]H_[c,d]` by a Hadamard-free word with an inverse. -/
theorem conj_hh : D8 n (P.map (NL.toPG n) ++ Hh n a b c d :: P'.map (NL.toPG n))
    (Hh n (permL P a) (permL P b) (permL P c) (permL P d) :: (twL n P c d ++ twL n P a b)) := by
  by_cases s1 : negL P a = negL P b <;> by_cases s2 : negL P c = negL P d
  · rw [twL_agree s1, twL_agree s2]
    exact hh_conj h8 hE hbd hbd' hpr hpr' hinv ha hb hc hd h s1 s2
  · obtain ⟨x, _y, hx6, -, -, ⟨hxa, hxb, hxc, hxd⟩, -⟩ := two_fresh a b c d
    rw [twL_agree s1, twL_disagree (bool_ne s2)]
    exact push_twist h8 hE hbd hbd' hpr hpr' hinv ha hb hc hd (by omega : x < 2 ^ n) h
      hxa hxb hxc hxd s1 (bool_ne s2)
  · rw [twL_disagree (bool_ne s1), twL_agree s2]
    exact conj_DA h8 hE hbd hbd' hpr hpr' hinv ha hb hc hd h (bool_ne s1) s2
  · rw [twL_disagree (bool_ne s1), twL_disagree (bool_ne s2)]
    exact conj_DD h8 hE hbd hbd' hpr hpr' hinv ha hb hc hd h (bool_ne s1) (bool_ne s2)

/-- The same with the conjugating word moved to the right. -/
theorem push_hh : D8 n (P.map (NL.toPG n) ++ [Hh n a b c d])
    (Hh n (permL P a) (permL P b) (permL P c) (permL P d) ::
      (twL n P c d ++ twL n P a b ++ P.map (NL.toPG n))) := by
  obtain ⟨-, c2⟩ := cancel_NL (n := n) (by omega) hbd hbd' hpr hpr' hinv
  have k := conj_hh h8 hE hbd hbd' hpr hpr' hinv ha hb hc hd h
  have k4 := DR.ctx (P.map (NL.toPG n) ++ [Hh n a b c d]) [] c2
  refine (DR.rfl' (by simp)).trans (k4.symm.trans ((DR.rfl' (by simp)).trans
    ((DR.right (P.map (NL.toPG n)) k).trans (DR.rfl' (by simp)))))

end Conj

end QCert.RealCliffordCH.Sec8
