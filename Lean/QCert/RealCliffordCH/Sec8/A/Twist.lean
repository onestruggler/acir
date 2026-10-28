/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Conjugating Hadamard-free letters, and the twist of Equation (40)

* Conjugation of signed permutations (`SP.conj_eq`), and of Hadamard-free
  words with natural-number indices by a word with an inverse (`conj_NL`): a
  sign pair `(-1)_[u](-1)_[v]` goes to the sign pair on the images
  (`conj_zz`), and `(-1)_[m]X_[c,d]` to `(-1)_[T m]X_[T c, T d]` when the signs of
  the conjugating word agree on `c, d` (`conj_zx`).
* The twist (`twist`): for distinct `a, b, c, d` and `x` away from them,
  `(-1)_[c](-1)_[x] · H_[a,b]H_[c,d] ≈ H_[a,b]H_[c,d] · (-1)_[c](-1)_[x] · (-1)_[d]X_[d,c]`,
  which is Equation (40) carried by the telescope of `(a,0), (b,1), (c,3),
  (d,2), (x,4)`.  A sign on one index of a pair changes the letter by a
  mixed letter; Equation (40) is the only rule of Figure 8 that says so.
-/
import QCert.RealCliffordCH.Sec8.A.Fig10b

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## Conjugation -/

theorem SP.conj_eq {N : ℕ} {τ τ' L M : SP N} (h1 : τ * τ' = 1)
    (hperm : ∀ j, M.perm (τ.perm j) = τ.perm (L.perm j))
    (hneg : ∀ j, M.neg (τ.perm j) = xor (xor (τ.neg (L.perm j)) (L.neg j)) (τ.neg j)) :
    τ * L * τ' = M := by
  have e : τ * L = M * τ := by
    apply SP.ext <;> funext j
    · simp [hperm]
    · simp only [SP.mul_neg, hneg]
      cases τ.neg (L.perm j) <;> cases L.neg j <;> cases τ.neg j <;> rfl
  rw [e, mul_assoc, h1, mul_one]

/-- Conjugation of a Hadamard-free word by one with an inverse, on natural-number
indices. -/
theorem conj_NL {T T' L M : List NL} (hT : ∀ y ∈ T, y.Bd n) (hT' : ∀ y ∈ T', y.Bd n)
    (hL : ∀ y ∈ L, y.Bd n) (hM : ∀ y ∈ M, y.Bd n)
    (hinv : ∀ v < 2 ^ n, permL (T ++ T') v = v ∧ negL (T ++ T') v = false)
    (hperm : ∀ j < 2 ^ n, permL M (permL T j) = permL T (permL L j))
    (hneg : ∀ j < 2 ^ n, negL M (permL T j) = xor (xor (negL T (permL L j)) (negL L j)) (negL T j)) :
    spW (wordOf ((T ++ L ++ T').map (NL.toPG n))) = spW (wordOf (M.map (NL.toPG n))) := by
  have h1 : spW (wordOf (T.map (NL.toPG n))) * spW (wordOf (T'.map (NL.toPG n))) = 1 := by
    rw [← spW_wordOf_append, ← List.map_append]
    exact spW_one_NL (fun y hy => (List.mem_append.1 hy).elim (hT y) (hT' y)) hinv
  rw [List.map_append, List.map_append, spW_wordOf_append, spW_wordOf_append]
  refine SP.conj_eq h1 (fun j => ?_) (fun j => ?_)
  · apply Fin.ext
    have hLj := (spW_NL hL j).1
    rw [(spW_NL hM _).1, (spW_NL hT j).1, (spW_NL hT _).1, hLj]
    exact hperm j j.2
  · have hLj := (spW_NL hL j).1
    rw [(spW_NL hM _).2, (spW_NL hT j).1, (spW_NL hT _).2, hLj, (spW_NL hL j).2,
      (spW_NL hT j).2]
    exact hneg j j.2

theorem conj_zz {T T' : List NL} (hT : ∀ y ∈ T, y.Bd n) (hT' : ∀ y ∈ T', y.Bd n)
    (hinv : ∀ v < 2 ^ n, permL (T ++ T') v = v ∧ negL (T ++ T') v = false) {u v : ℕ}
    (hu : u < 2 ^ n) (hv : v < 2 ^ n) :
    spW (wordOf ((T ++ [NL.zz u v] ++ T').map (NL.toPG n))) =
      spW (wordOf ([NL.zz (permL T u) (permL T v)].map (NL.toPG n))) := by
  have inj := permL_inj T
  refine conj_NL hT hT' (by simp [NL.Bd, hu, hv])
    (by simp [NL.Bd, permL_lt hT hu, permL_lt hT hv]) hinv (fun j _ => rfl) (fun j _ => ?_)
  simp only [negL, permL, id, NL.neg, NL.perm, inj.eq_iff]
  by_cases h1 : j = u <;> by_cases h2 : j = v <;> cases negL T j <;> simp [h1, h2]

theorem conj_zx {T T' : List NL} (hT : ∀ y ∈ T, y.Bd n) (hT' : ∀ y ∈ T', y.Bd n)
    (hinv : ∀ v < 2 ^ n, permL (T ++ T') v = v ∧ negL (T ++ T') v = false) {m c d : ℕ}
    (hm : m < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hs : negL T c = negL T d) :
    spW (wordOf ((T ++ [NL.zx m c d] ++ T').map (NL.toPG n))) =
      spW (wordOf ([NL.zx (permL T m) (permL T c) (permL T d)].map (NL.toPG n))) := by
  have inj := permL_inj T
  have hsw : ∀ j, swN (permL T c) (permL T d) (permL T j) = permL T (swN c d j) := by
    intro j
    by_cases h1 : j = c
    · subst h1; simp [swN]
    · by_cases h2 : j = d
      · subst h2; simp [swN, inj.eq_iff, h1]
      · simp [swN, inj.eq_iff, h1, h2]
  refine conj_NL hT hT' (by simp [NL.Bd, hm, hc, hd])
    (by simp [NL.Bd, permL_lt hT hm, permL_lt hT hc, permL_lt hT hd]) hinv
    (fun j _ => by simp only [permL, NL.perm, id]; exact hsw j) (fun j _ => ?_)
  have hsg : negL T (swN c d j) = negL T j := by
    unfold swN
    by_cases h1 : j = c
    · subst h1; simp [hs]
    · by_cases h2 : j = d
      · subst h2; simp [h1, hs]
      · simp [h1, h2]
  simp only [negL, permL, id, NL.neg, NL.perm, hsw, inj.eq_iff, hsg]
  by_cases h1 : swN c d j = m <;> cases negL T j <;> simp [h1]

theorem conj_mul {M : Type*} [Monoid M] {t t' A B : M} (h : t' * t = 1) :
    t * (A * B) * t' = (t * A * t') * (t * B * t') := by
  calc t * (A * B) * t' = t * A * (t' * t) * B * t' := by rw [h, mul_one]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-! ## Equation (40) and the twist -/

/-- Equation (40). -/
theorem e40 : D8 n [Zz n 3 4, Lam n] [Lam n, Zz n 3 4, Zx n 2 2 3] := DR.ax (Fig8.r40 (n := n))

/-- The twist: a sign on the first index of the second pair of a letter. -/
theorem twist (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d x : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hx : x < 2 ^ n) (h : Distinct4 a b c d)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d) :
    D8 n [Zz n c x, Hh n a b c d] [Hh n a b c d, Zz n c x, Zx n d d c] := by
  have hN : 4 ≤ 2 ^ n := by omega
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h
  set P : List (ℕ × ℕ) := [(a, 0), (b, 1), (c, 3), (d, 2), (x, 4)]
  have hok : PlanOk P := by
    refine ⟨?_, by simp [P]⟩
    simp [P, d1, d2, d3, d4, d5, d6, Ne.symm hxa, Ne.symm hxb, Ne.symm hxc, Ne.symm hxd]
  have hbdP : PlanBd (2 ^ n) P := by
    intro q hq
    simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by assumption, by omega⟩
  have h5 : (5 : ℕ) < 2 ^ n := by omega
  obtain ⟨b1, b2⟩ := telNL_bd h5 P hbdP
  have hinv : ∀ v < 2 ^ n, permL (telNL 5 P ++ telNL' 5 P) v = v ∧
      negL (telNL 5 P ++ telNL' 5 P) v = false := fun v _ => telNL_inv 5 P v
  have hρ : ∀ y k, (y, k) ∈ P → permL (telNL 5 P) k = y := fun y k hm => by
    rw [permL_telNL, rho_mem P hok y k hm]
  have FT : Frame n a b c d ((telNL 5 P).map (NL.toPG n)) ((telNL' 5 P).map (NL.toPG n)) :=
    Frame.tel hN hok hbdP h5 (by norm_num) (by simp [P]) (by simp [P]) (by simp [P]) (by simp [P])
  set T := (telNL 5 P).map (NL.toPG n)
  set T' := (telNL' 5 P).map (NL.toPG n)
  have k := hh_frame h8 hE ha hb hc hd ⟨d1, d2, d3, d4, d5, d6⟩ FT
  obtain ⟨c1, c2⟩ := frame_cancel hN FT
  have hHPT := FT.hA
  have hHPT' := FT.hA'
  have hpz : ∀ u v : ℕ, HP [Zz n u v] := fun u v y hy => by
    simp only [List.mem_singleton] at hy; subst hy; exact ⟨trivial, trivial⟩
  have hpzx : ∀ u v w : ℕ, u < 2 ^ n → v < 2 ^ n → w < 2 ^ n → v ≠ w → HP [Zx n u v w] :=
    fun u v w hu hv hw hvw y hy => by
      simp only [List.mem_singleton] at hy; subst hy
      refine ⟨trivial, fun e => hvw ?_⟩
      have := congrArg Fin.val e; rwa [ix_val hv, ix_val hw] at this
  have ezz : spW (wordOf (T ++ [Zz n 3 4] ++ T')) = spW (wordOf [Zz n c x]) := by
    have := conj_zz (n := n) b1 b2 hinv (u := 3) (v := 4) (by omega) (by omega)
    rw [hρ c 3 (by simp [P]), hρ x 4 (by simp [P])] at this
    simpa only [List.map_append, List.map_cons, List.map_nil, NL.toPG] using this
  have hs : negL (telNL 5 P) 2 = negL (telNL 5 P) 3 := by
    rw [negL_telNL 5 P 2 (by norm_num), negL_telNL 5 P 3 (by norm_num)]
  have ezx : spW (wordOf (T ++ [Zx n 2 2 3] ++ T')) = spW (wordOf [Zx n d d c]) := by
    have := conj_zx (n := n) b1 b2 hinv (m := 2) (c := 2) (d := 3) (by omega) (by omega)
      (by omega) hs
    rw [hρ d 2 (by simp [P]), hρ c 3 (by simp [P])] at this
    simpa only [List.map_append, List.map_cons, List.map_nil, NL.toPG] using this
  -- `(-1)_[c](-1)_[x] ≈ T (-1)_[3](-1)_[4] T'`
  have z1 : D8 n [Zz n c x] (T ++ [Zz n 3 4] ++ T') :=
    A5s hN (hpz c x) ((hHPT.append (hpz 3 4)).append hHPT') ezz.symm
  -- `T (-1)_[3](-1)_[4] (-1)_[2]X_[2,3] T' ≈ (-1)_[c](-1)_[x] (-1)_[d]X_[d,c]`
  have z2 : D8 n (T ++ [Zz n 3 4, Zx n 2 2 3] ++ T') [Zz n c x, Zx n d d c] := by
    refine A5s hN ((hHPT.append ((hpz 3 4).append (hpzx 2 2 3 (by omega) (by omega)
      (by omega) (by norm_num)))).append hHPT') ((hpz c x).append (hpzx d d c hd hd hc
        (Ne.symm d6))) ?_
    have ht : spW (wordOf T') * spW (wordOf T) = 1 := by
      rw [← spW_wordOf_append]; exact inv_comm FT.inv
    rw [show T ++ [Zz n 3 4, Zx n 2 2 3] ++ T' = T ++ ([Zz n 3 4] ++ [Zx n 2 2 3]) ++ T' from rfl,
      show ([Zz n c x, Zx n d d c] : List (PG (2 ^ n))) = [Zz n c x] ++ [Zx n d d c] from rfl]
    simp only [spW_wordOf_append] at ezz ezx ⊢
    rw [conj_mul ht, ezz, ezx]
  -- the chain
  refine (DR.append z1 k).trans ?_
  refine (DR.rfl' (by simp)).trans ((DR.ctx (T ++ [Zz n 3 4]) (Lam n :: T') c1).trans ?_)
  refine (DR.rfl' (by simp)).trans ((DR.ctx T T' e40).trans ?_)
  refine (DR.rfl' (by simp)).trans ((DR.ctx (T ++ [Lam n]) ([Zz n 3 4, Zx n 2 2 3] ++ T')
    c1.symm).trans ?_)
  refine (DR.rfl' (by simp)).trans ((DR.append k.symm z2).trans (DR.rfl' (by simp)))

end QCert.RealCliffordCH.Sec8
