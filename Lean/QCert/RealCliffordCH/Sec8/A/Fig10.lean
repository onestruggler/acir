/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Figure 10 (Corollary A.8), from Equation (65)

The equations of Figure 10, each derived from Equation (65) (`E65`, which
`Frame` reduces to Equation (35) for the tuples whose Gray codes have
neither form of (36), (37)) with Corollary A.7 in the form of `frame_eq`
and `frame_swap`:

* (66) `H_[a,b]H_[c,d] ≈ H_[c,d]H_[a,b]` is in `Frame`;
* (70) `H_[a,b]H_[a,b] ≈ ε`: Equation (42) splits the letter over a fresh
  pair `e, f`, the two halves are `A Λ A'` for one frame, and `Λ Λ ≈ ε` (41);
* (71) `H_[a,b]H_[c,d] · H_[c,d]H_[e,f] ≈ H_[a,b]H_[e,f]` for six distinct
  indices: with `T` the telescope of `(a,0), (b,1), (c,3), (d,2), (e,4), (f,5)`,
  the two letters are `T Λ T'` and `T (Σ_{3,2,4,5} Λ Σ'_{3,2,4,5}) T'`, and
  Equation (43) turns `Λ · H_[3,2]H_[4,5]` into its conjugate by
  `X_[0,3]X_[1,2]`, which `T` carries to `H_[a,b]H_[e,f]`.
-/
import QCert.RealCliffordCH.Sec8.A.Frame

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## Conjugating a frame -/

/-- A frame conjugated by a Hadamard-free word with an inverse is a frame. -/
theorem Frame.conjNL {x0 x1 x3 x2 : ℕ} {V V' : List (PG (2 ^ n))}
    (hV : Frame n x0 x1 x3 x2 V V') (h0 : x0 < 2 ^ n) (h1 : x1 < 2 ^ n) (h3 : x3 < 2 ^ n)
    (h2 : x2 < 2 ^ n) {T T' : List NL} (hbd : ∀ y ∈ T, y.Bd n) (hbd' : ∀ y ∈ T', y.Bd n)
    (hpr : ∀ y ∈ T, y.Pr) (hpr' : ∀ y ∈ T', y.Pr)
    (hinv : ∀ v < 2 ^ n, permL (T ++ T') v = v ∧ negL (T ++ T') v = false)
    (hs01 : negL T x0 = negL T x1) (hs32 : negL T x3 = negL T x2) :
    Frame n (permL T x0) (permL T x1) (permL T x3) (permL T x2)
      (T.map (NL.toPG n) ++ V) (V' ++ T'.map (NL.toPG n)) := by
  have key : ∀ (j x : ℕ), x < 2 ^ n → ((spW (wordOf V)).perm (ix n j) : ℕ) = x →
      ((spW (wordOf (T.map (NL.toPG n) ++ V))).perm (ix n j) : ℕ) = permL T x ∧
      (spW (wordOf (T.map (NL.toPG n) ++ V))).neg (ix n j) =
        xor (negL T x) ((spW (wordOf V)).neg (ix n j)) := by
    intro j x hx hv
    have e : (spW (wordOf V)).perm (ix n j) = ix n x := Fin.ext (hv.trans (ix_val hx).symm)
    rw [spW_wordOf_append, SP.mul_perm, SP.mul_neg, e]
    obtain ⟨f1, f2⟩ := spW_NL hbd (ix n x)
    rw [ix_val hx] at f1 f2
    exact ⟨f1, by rw [f2]⟩
  obtain ⟨p0, n0⟩ := key 0 x0 h0 hV.i0
  obtain ⟨p1, n1⟩ := key 1 x1 h1 hV.i1
  obtain ⟨p3, n3⟩ := key 3 x3 h3 hV.i3
  obtain ⟨p2, n2⟩ := key 2 x2 h2 hV.i2
  refine ⟨(HP_NL hbd hpr).append hV.hA, hV.hA'.append (HP_NL hbd' hpr'), ?_, p0, p1, p3, p2,
    ?_, ?_⟩
  · have hT : spW (wordOf (T.map (NL.toPG n) ++ T'.map (NL.toPG n))) = 1 := by
      rw [← List.map_append]
      exact spW_one_NL (fun x hx => (List.mem_append.1 hx).elim (hbd x) (hbd' x)) hinv
    rw [show T.map (NL.toPG n) ++ V ++ (V' ++ T'.map (NL.toPG n)) =
      T.map (NL.toPG n) ++ ((V ++ V') ++ T'.map (NL.toPG n)) by simp,
      spW_wordOf_append, spW_wordOf_append, hV.inv, one_mul, ← spW_wordOf_append, hT]
  · rw [n0, n1, hs01, hV.s01]
  · rw [n3, n2, hs32, hV.s32]

/-! ## Equation (42): a fresh pair -/

theorem two_fresh (a b c d : ℕ) : ∃ x y, x < 6 ∧ y < 6 ∧ x ≠ y ∧
    (x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d) ∧ (y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ y ≠ d) := by
  set S : Finset ℕ := {a, b, c, d}
  have hS : S.card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  have h := Finset.card_le_card_sdiff_add_card (s := Finset.range 6) (t := S)
  rw [Finset.card_range] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (show 1 < (Finset.range 6 \ S).card by omega)
  simp only [S, Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton,
    not_or] at hx hy
  exact ⟨x, y, hx.1, hy.1, hxy, hx.2, hy.2⟩

theorem list_two {l : List ℕ} (hnd : l.Nodup) {x y : ℕ} (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) :
    ∃ e f rest, l = e :: f :: rest := by
  rcases l with _ | ⟨e, _ | ⟨f, rest⟩⟩
  · simp at hx
  · simp at hx hy; exact absurd (hx.trans hy.symm) hxy
  · exact ⟨e, f, rest, rfl⟩

/-- `freshPair` gives two distinct indices away from `a, b, c, d`. -/
theorem freshPair_spec (h6 : 6 ≤ 2 ^ n) (a b c d : ℕ) :
    ∃ e f, freshPair n a b c d = (e, f) ∧ e < 2 ^ n ∧ f < 2 ^ n ∧ e ≠ f ∧
      (e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d) ∧ (f ≠ a ∧ f ≠ b ∧ f ≠ c ∧ f ≠ d) := by
  obtain ⟨x, y, hx, hy, hxy, hxa, hya⟩ := two_fresh a b c d
  have hnd : ((List.range (2 ^ n)).filter (fun e => e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d)).Nodup :=
    List.nodup_range.filter _
  have hmem : ∀ z, z ∈ (List.range (2 ^ n)).filter (fun e => e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d) ↔
      z < 2 ^ n ∧ (z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d) := fun z => by simp
  obtain ⟨e, f, rest, hl⟩ := list_two hnd ((hmem x).2 ⟨by omega, hxa⟩) ((hmem y).2 ⟨by omega, hya⟩)
    hxy
  have he := (hmem e).1 (by rw [hl]; simp)
  have hf := (hmem f).1 (by rw [hl]; simp)
  have hef : e ≠ f := by
    have := hl ▸ hnd
    simp only [List.nodup_cons, List.mem_cons, not_or] at this
    exact this.1.1
  refine ⟨e, f, ?_, he.1, hf.1, hef, he.2, hf.2⟩
  simp only [freshPair, hl]

/-! ## Equations (41), (43), (70) -/

/-- Equation (41). -/
theorem e41 : D8 n [Lam n, Lam n] [] := DR.ax (Fig8.r41 (n := n))

/-- Equation (43). -/
theorem e43 : D8 n [Lam n, Hh n 3 2 4 5] [Xx n 0 3 1 2, Hh n 3 2 4 5, Xx n 0 3 1 2] :=
  DR.ax (Fig8.r43 (n := n))

/-- Equation (70): `H_[a,b]H_[a,b] ≈ ε`. -/
theorem e70 (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hab : a ≠ b) : D8 n [Hh n a b a b] [] := by
  obtain ⟨e, f, hp, he, hf, hef, hea, hfa⟩ := freshPair_spec (n := n) (by omega) a b a b
  have h42 : D8 n [Hh n a b e f, Hh n e f a b] [Hh n a b a b] := by
    have := DR.ax (Γ := Fig8 n) (Fig8.r42 a b a b ha hb ha hb hab hab (fun h => h.2.1 rfl))
    simpa only [hp] using this
  have hd : Distinct4 a b e f :=
    ⟨hab, Ne.symm hea.1, Ne.symm hfa.1, Ne.symm hea.2.1, Ne.symm hfa.2.1, hef⟩
  have F := Frame.sigma h8 ha hb he hf hd
  have F' := Frame.sigma h8 he hf ha hb hd.swap
  have h1 := hh_frame h8 hE ha hb he hf hd F
  have h2 := (hE e f a b he hf ha hb hd.swap).trans (frame_swap (by omega) F' F)
  obtain ⟨c1, c2⟩ := frame_cancel (by omega) F
  set A := (sigmaW n a b e f).1
  set A' := (sigmaW n a b e f).2
  refine h42.symm.trans ((DR.append h1 h2).trans ?_)
  refine (DR.rfl' (by simp)).trans ((DR.ctx (A ++ [Lam n]) (Lam n :: A') c1).trans ?_)
  refine (DR.rfl' (by simp)).trans ((DR.ctx A A' e41).trans ?_)
  exact (DR.rfl' (by simp)).trans c2

/-! ## Equation (71) for six distinct indices -/

/-- The plan of `T_{a,b,c,d,e,f}`. -/
def tPlan (a b c d e f : ℕ) : List (ℕ × ℕ) := [(a, 0), (b, 1), (c, 3), (d, 2), (e, 4), (f, 5)]

theorem permL_xx0312 (v : ℕ) : permL [NL.xx 0 3 1 2] v = swN 0 3 (swN 1 2 v) := rfl

theorem negL_xx0312 (v : ℕ) : negL [NL.xx 0 3 1 2] v = false := by
  simp [negL, NL.neg]

/-- Equation (71) when the six indices are distinct. -/
theorem e71_distinct (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d e f : ℕ} (ha : a < 2 ^ n)
    (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n) (he : e < 2 ^ n) (hf : f < 2 ^ n)
    (hnd : [a, b, c, d, e, f].Nodup) :
    D8 n [Hh n a b c d, Hh n c d e f] [Hh n a b e f] := by
  have hN : 4 ≤ 2 ^ n := by omega
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩ := hnd
  set P := tPlan a b c d e f
  have hok : PlanOk P := by
    refine ⟨?_, by simp [P, tPlan]⟩
    simp [P, tPlan, hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef]
  have hbdP : PlanBd (2 ^ n) P := by
    intro q hq
    simp only [P, tPlan, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by assumption, by omega⟩
  have h6 : (6 : ℕ) < 2 ^ n := by omega
  obtain ⟨b1, b2⟩ := telNL_bd h6 P hbdP
  obtain ⟨r1, r2⟩ := telNL_pr 6 P
  have hρ : ∀ x k, (x, k) ∈ P → permL (telNL 6 P) k = x := fun x k h => by
    rw [permL_telNL, rho_mem P hok x k h]
  have hs : ∀ v, v ≠ 6 → negL (telNL 6 P) v = false := fun v hv => negL_telNL 6 P v hv
  set T := telNL 6 P
  set T' := telNL' 6 P
  -- the frames
  have FT : Frame n a b c d (T.map (NL.toPG n)) (T'.map (NL.toPG n)) :=
    Frame.tel hN hok hbdP h6 (by norm_num) (by simp [P, tPlan]) (by simp [P, tPlan])
      (by simp [P, tPlan]) (by simp [P, tPlan])
  have hd3245 : Distinct4 3 2 4 5 := by decide
  have FV := Frame.sigma h8 (show (3 : ℕ) < 2 ^ n by omega) (show (2 : ℕ) < 2 ^ n by omega)
    (show (4 : ℕ) < 2 ^ n by omega) (show (5 : ℕ) < 2 ^ n by omega) hd3245
  set V := (sigmaW n 3 2 4 5).1
  set V' := (sigmaW n 3 2 4 5).2
  have FC : Frame n c d e f (T.map (NL.toPG n) ++ V) (V' ++ T'.map (NL.toPG n)) := by
    have := Frame.conjNL FV (by omega) (by omega) (by omega) (by omega) b1 b2 r1 r2
      (fun v _ => telNL_inv 6 P v) (by rw [hs 3 (by norm_num), hs 2 (by norm_num)])
      (by rw [hs 4 (by norm_num), hs 5 (by norm_num)])
    rwa [hρ c 3 (by simp [P, tPlan]), hρ d 2 (by simp [P, tPlan]), hρ e 4 (by simp [P, tPlan]),
      hρ f 5 (by simp [P, tPlan])] at this
  have FE : Frame n a b e f ((T ++ [NL.xx 0 3 1 2]).map (NL.toPG n) ++ V)
      (V' ++ ([NL.xx 0 3 1 2] ++ T').map (NL.toPG n)) := by
    have bx : ∀ y ∈ [NL.xx 0 3 1 2], y.Bd n := by
      intro y hy; simp only [List.mem_singleton] at hy; subst hy
      exact ⟨by omega, by omega, by omega, by omega⟩
    have px : ∀ y ∈ [NL.xx 0 3 1 2], y.Pr := by
      intro y hy; simp only [List.mem_singleton] at hy; subst hy
      exact ⟨by norm_num, by norm_num⟩
    have hinv : ∀ v < 2 ^ n, permL (T ++ [NL.xx 0 3 1 2] ++ ([NL.xx 0 3 1 2] ++ T')) v = v ∧
        negL (T ++ [NL.xx 0 3 1 2] ++ ([NL.xx 0 3 1 2] ++ T')) v = false := by
      intro v _
      have e1 : T ++ [NL.xx 0 3 1 2] ++ ([NL.xx 0 3 1 2] ++ T') =
          T ++ ([NL.xx 0 3 1 2, NL.xx 0 3 1 2] ++ T') := by simp
      have hp : ∀ w, permL ([NL.xx 0 3 1 2, NL.xx 0 3 1 2] ++ T') w = permL T' w := fun w => by
        rw [permL_append, (NL.inv_xx0312 _).1]
      have hn : ∀ w, negL ([NL.xx 0 3 1 2, NL.xx 0 3 1 2] ++ T') w = negL T' w := fun w => by
        rw [negL_append, (NL.inv_xx0312 _).2]; exact Bool.false_xor _
      rw [e1]
      refine ⟨?_, ?_⟩
      · rw [permL_append, hp, ← permL_append]; exact (telNL_inv 6 P v).1
      · rw [negL_append, hp, hn, ← negL_append]; exact (telNL_inv 6 P v).2
    have hval : ∀ x k w, (x, k) ∈ P → swN 0 3 (swN 1 2 w) = k →
        permL (T ++ [NL.xx 0 3 1 2]) w = x := fun x k w h hw => by
      rw [permL_append, permL_xx0312, hw, hρ x k h]
    have hneg : ∀ w, swN 0 3 (swN 1 2 w) ≠ 6 → negL (T ++ [NL.xx 0 3 1 2]) w = false :=
      fun w hw => by rw [negL_append, permL_xx0312, hs _ hw, negL_xx0312]; rfl
    have := Frame.conjNL FV (by omega) (by omega) (by omega) (by omega)
      (fun y hy => (List.mem_append.1 hy).elim (b1 y) (bx y))
      (fun y hy => (List.mem_append.1 hy).elim (bx y) (b2 y))
      (fun y hy => (List.mem_append.1 hy).elim (r1 y) (px y))
      (fun y hy => (List.mem_append.1 hy).elim (px y) (r2 y)) hinv
      (by rw [hneg 3 (by decide), hneg 2 (by decide)])
      (by rw [hneg 4 (by decide), hneg 5 (by decide)])
    rwa [hval a 0 3 (by simp [P, tPlan]) (by decide), hval b 1 2 (by simp [P, tPlan]) (by decide),
      hval e 4 4 (by simp [P, tPlan]) (by decide), hval f 5 5 (by simp [P, tPlan]) (by decide)]
      at this
  -- the chain
  have hcdef : Distinct4 c d e f := ⟨hcd, hce, hcf, hde, hdf, hef⟩
  have hab' : Distinct4 a b c d := ⟨hab, hac, had, hbc, hbd, hcd⟩
  have habef : Distinct4 a b e f := ⟨hab, hae, haf, hbe, hbf, hef⟩
  have k1 := hh_frame h8 hE ha hb hc hd hab' FT
  have k2 := hh_frame h8 hE hc hd he hf hcdef FC
  have k3 := hh_frame h8 hE ha hb he hf habef FE
  have kV := hh_frame h8 hE (show (3 : ℕ) < 2 ^ n by omega) (show (2 : ℕ) < 2 ^ n by omega)
    (show (4 : ℕ) < 2 ^ n by omega) (show (5 : ℕ) < 2 ^ n by omega) hd3245 FV
  obtain ⟨c1, _⟩ := frame_cancel hN FT
  set Tm := T.map (NL.toPG n)
  set T'm := T'.map (NL.toPG n)
  have s1 : D8 n [Hh n a b c d, Hh n c d e f]
      (Tm ++ [Lam n] ++ (T'm ++ Tm) ++ (V ++ Lam n :: (V' ++ T'm))) :=
    (DR.append k1 k2).trans (DR.rfl' (by simp))
  have s2 : D8 n (Tm ++ [Lam n] ++ (T'm ++ Tm) ++ (V ++ Lam n :: (V' ++ T'm)))
      (Tm ++ [Lam n] ++ [Hh n 3 2 4 5] ++ T'm) :=
    (DR.ctx (Tm ++ [Lam n]) (V ++ Lam n :: (V' ++ T'm)) c1).trans <|
      (DR.rfl' (by simp)).trans ((DR.ctx (Tm ++ [Lam n]) T'm kV.symm).trans (DR.rfl' (by simp)))
  have s3 : D8 n (Tm ++ [Lam n] ++ [Hh n 3 2 4 5] ++ T'm)
      ((Tm ++ [Xx n 0 3 1 2] ++ V) ++ Lam n :: (V' ++ ([Xx n 0 3 1 2] ++ T'm))) :=
    (DR.rfl' (by simp)).trans <| (DR.ctx Tm T'm e43).trans <|
      (DR.rfl' (by simp)).trans <| (DR.ctx (Tm ++ [Xx n 0 3 1 2]) (Xx n 0 3 1 2 :: T'm) kV).trans
        (DR.rfl' (by simp))
  have s4 : D8 n ((Tm ++ [Xx n 0 3 1 2] ++ V) ++ Lam n :: (V' ++ ([Xx n 0 3 1 2] ++ T'm)))
      [Hh n a b e f] := by
    have := k3.symm
    simpa [Tm, T'm, List.map_append, NL.toPG] using this
  exact s1.trans (s2.trans (s3.trans s4))

end QCert.RealCliffordCH.Sec8
