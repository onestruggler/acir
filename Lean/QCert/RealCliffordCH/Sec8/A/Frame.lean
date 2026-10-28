/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Frames: `H_[a,b]H_[c,d]` written as `A Λ A'`

A frame for `(a, b, c, d)` (`Frame`) is a pair of proper Hadamard-free words
`A`, `A'` with `A A'` the identity, whose signed permutation sends `0, 1, 3, 2`
to `a, b, c, d` with the same sign on `0` and `1` and on `3` and `2`; then
`A Λ A'` denotes `H_[a,b]H_[c,d]`.  By Corollary A.7 any two frames for the
same tuple give derivably equal words (`frame_eq`), and so do frames for
`(a, b, c, d)` and `(c, d, a, b)` (`frame_swap`).

Telescopes (`telNL`) build frames: a plan lists pairs (target, numeral), and
the word is the product of the letters `(-1)_[m] X_[x, ρ(k)]`, each moving its
numeral to its target, with its sign on the image of a spare numeral `s`.
Definition E.1's `Σ_{a,b,c,d}`, `Σ'_{a,b,c,d}` is the telescope of the plan
`(a,0), (b,1), (c,3), (d,2)` with spare `4` (`sigmaW_eq`), so Equation (35) is
`H_[a,b]H_[c,d] ≈ A Λ A'` for one frame, and hence for every frame.  `E65`
is Equation (65): the same at every tuple of distinct indices, whatever the
form of its Gray codes.
-/
import QCert.RealCliffordCH.Sec8.A.A6

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## One-sided inverses of signed permutations -/

theorem SP.mul_eq_one_comm {N : ℕ} {X Y : SP N} (hX : Function.Injective X.perm)
    (h : X * Y = 1) : Y * X = 1 := by
  have hp : ∀ j, X.perm (Y.perm j) = j := fun j => by
    simpa using congrFun (congrArg SP.perm h) j
  have hn : ∀ j, xor (X.neg (Y.perm j)) (Y.neg j) = false := fun j => by
    simpa using congrFun (congrArg SP.neg h) j
  have hp' : ∀ j, Y.perm (X.perm j) = j := fun j => hX (hp (X.perm j))
  apply SP.ext <;> funext j
  · exact hp' j
  · show xor (Y.neg (X.perm j)) (X.neg j) = false
    have := hn (X.perm j)
    rw [hp'] at this
    revert this; cases X.neg j <;> cases Y.neg (X.perm j) <;> simp

/-! ## Frames -/

/-- A frame for `(a, b, c, d)`: `A Λ A'` denotes `H_[a,b]H_[c,d]`. -/
structure Frame (n a b c d : ℕ) (A A' : List (PG (2 ^ n))) : Prop where
  hA : HP A
  hA' : HP A'
  inv : spW (wordOf (A ++ A')) = 1
  i0 : ((spW (wordOf A)).perm (ix n 0) : ℕ) = a
  i1 : ((spW (wordOf A)).perm (ix n 1) : ℕ) = b
  i3 : ((spW (wordOf A)).perm (ix n 3) : ℕ) = c
  i2 : ((spW (wordOf A)).perm (ix n 2) : ℕ) = d
  s01 : (spW (wordOf A)).neg (ix n 0) = (spW (wordOf A)).neg (ix n 1)
  s32 : (spW (wordOf A)).neg (ix n 3) = (spW (wordOf A)).neg (ix n 2)

theorem inv_comm {A A' : List (PG (2 ^ n))} (h : spW (wordOf (A ++ A')) = 1) :
    spW (wordOf (A' ++ A)) = 1 := by
  rw [spW_wordOf_append] at h ⊢
  exact SP.mul_eq_one_comm (spW_perm_bij _).1 h

theorem frame_aux {A B B' : List (PG (2 ^ n))} (hB : spW (wordOf (B ++ B')) = 1)
    {j k : Fin (2 ^ n)} (h : (spW (wordOf A)).perm j = (spW (wordOf B)).perm k) :
    (spW (wordOf (B' ++ A))).perm j = k ∧
      (spW (wordOf (B' ++ A))).neg j = xor ((spW (wordOf B)).neg k) ((spW (wordOf A)).neg j) := by
  have h' := inv_comm hB
  rw [spW_wordOf_append] at h'
  have hp : (spW (wordOf B')).perm ((spW (wordOf B)).perm k) = k := by
    simpa using congrFun (congrArg SP.perm h') k
  have hn : xor ((spW (wordOf B')).neg ((spW (wordOf B)).perm k)) ((spW (wordOf B)).neg k) =
      false := by simpa using congrFun (congrArg SP.neg h') k
  rw [spW_wordOf_append, SP.mul_perm, SP.mul_neg, h, hp]
  refine ⟨rfl, ?_⟩
  congr 1
  revert hn; cases (spW (wordOf B')).neg ((spW (wordOf B)).perm k) <;>
    cases (spW (wordOf B)).neg k <;> simp

theorem fin_eq_of_val {N : ℕ} {i j : Fin N} {v : ℕ} (hi : (i : ℕ) = v) (hj : (j : ℕ) = v) : i = j :=
  Fin.ext (hi.trans hj.symm)

/-- Two frames for the same tuple give derivably equal words (Corollary A.7). -/
theorem frame_eq (hN : 4 ≤ 2 ^ n) {a b c d : ℕ} {A A' B B' : List (PG (2 ^ n))}
    (hA : Frame n a b c d A A') (hB : Frame n a b c d B B') :
    D8 n (A ++ Lam n :: A') (B ++ Lam n :: B') := by
  refine A7 hN hA.hA hA.hA' hB.hA hB.hA' hA.inv hB.inv ?_
  have v : ∀ j < 4, ((ix n j : Fin (2 ^ n)) : ℕ) = j := fun j hj => ix_val (by omega)
  obtain ⟨p0, n0⟩ := frame_aux hB.inv (fin_eq_of_val hA.i0 hB.i0)
  obtain ⟨p1, n1⟩ := frame_aux hB.inv (fin_eq_of_val hA.i1 hB.i1)
  obtain ⟨p3, n3⟩ := frame_aux hB.inv (fin_eq_of_val hA.i3 hB.i3)
  obtain ⟨p2, n2⟩ := frame_aux hB.inv (fin_eq_of_val hA.i2 hB.i2)
  refine ⟨Or.inl ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [p0, v 0 (by norm_num)]
  · rw [p1, v 1 (by norm_num)]
  · rw [p3, v 3 (by norm_num)]
  · rw [p2, v 2 (by norm_num)]
  · rw [n0, n1, hA.s01, hB.s01]
  · rw [n3, n2, hA.s32, hB.s32]

/-- Frames for `(a, b, c, d)` and `(c, d, a, b)` give derivably equal words. -/
theorem frame_swap (hN : 4 ≤ 2 ^ n) {a b c d : ℕ} {A A' B B' : List (PG (2 ^ n))}
    (hA : Frame n a b c d A A') (hB : Frame n c d a b B B') :
    D8 n (A ++ Lam n :: A') (B ++ Lam n :: B') := by
  refine A7 hN hA.hA hA.hA' hB.hA hB.hA' hA.inv hB.inv ?_
  have v : ∀ j < 4, ((ix n j : Fin (2 ^ n)) : ℕ) = j := fun j hj => ix_val (by omega)
  obtain ⟨p0, n0⟩ := frame_aux hB.inv (fin_eq_of_val hA.i0 hB.i3)
  obtain ⟨p1, n1⟩ := frame_aux hB.inv (fin_eq_of_val hA.i1 hB.i2)
  obtain ⟨p3, n3⟩ := frame_aux hB.inv (fin_eq_of_val hA.i3 hB.i0)
  obtain ⟨p2, n2⟩ := frame_aux hB.inv (fin_eq_of_val hA.i2 hB.i1)
  refine ⟨Or.inr ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [p0, v 3 (by norm_num)]
  · rw [p1, v 2 (by norm_num)]
  · rw [p3, v 0 (by norm_num)]
  · rw [p2, v 1 (by norm_num)]
  · rw [n0, n1, hA.s01, hB.s32]
  · rw [n3, n2, hA.s32, hB.s01]

/-- The two halves of a frame cancel. -/
theorem frame_cancel (hN : 4 ≤ 2 ^ n) {a b c d : ℕ} {A A' : List (PG (2 ^ n))}
    (hA : Frame n a b c d A A') : D8 n (A' ++ A) [] ∧ D8 n (A ++ A') [] :=
  ⟨A5s hN (hA.hA'.append hA.hA) HP.nil (by rw [inv_comm hA.inv, spW_nil]),
    A5s hN (hA.hA.append hA.hA') HP.nil (by rw [hA.inv, spW_nil])⟩

/-! ## Frames from letters with natural-number indices -/

/-- An `NL` letter whose two-level matrices are on distinct indices. -/
def NL.Pr : NL → Prop
  | .zz _ _ => True
  | .zx _ c d => c ≠ d
  | .xx a b c d => a ≠ b ∧ c ≠ d

theorem HP_NL {A : List NL} (hbd : ∀ x ∈ A, x.Bd n) (hpr : ∀ x ∈ A, x.Pr) :
    HP (A.map (NL.toPG n)) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have hb := hbd x hx
  have hp := hpr x hx
  cases x with
  | zz a c => exact ⟨trivial, trivial⟩
  | zx a c d =>
    refine ⟨trivial, fun h => hp ?_⟩
    have := congrArg Fin.val h
    rwa [ix_val hb.2.1, ix_val hb.2.2] at this
  | xx a b c d =>
    refine ⟨trivial, fun h => hp.1 ?_, fun h => hp.2 ?_⟩
    · have := congrArg Fin.val h
      rwa [ix_val hb.1, ix_val hb.2.1] at this
    · have := congrArg Fin.val h
      rwa [ix_val hb.2.2.1, ix_val hb.2.2.2] at this

theorem spW_one_NL {L : List NL} (hbd : ∀ x ∈ L, x.Bd n)
    (h : ∀ v < 2 ^ n, permL L v = v ∧ negL L v = false) : spW (wordOf (L.map (NL.toPG n))) = 1 :=
  (spW_eq_of_NL (l' := []) hbd (by simp) fun v hv => h v hv).trans spW_nil

theorem Frame.ofNL (hN : 4 ≤ 2 ^ n) {a b c d : ℕ} {A A' : List NL} (hbd : ∀ x ∈ A, x.Bd n)
    (hbd' : ∀ x ∈ A', x.Bd n) (hpr : ∀ x ∈ A, x.Pr) (hpr' : ∀ x ∈ A', x.Pr)
    (hinv : ∀ v < 2 ^ n, permL (A ++ A') v = v ∧ negL (A ++ A') v = false)
    (h0 : permL A 0 = a) (h1 : permL A 1 = b) (h3 : permL A 3 = c) (h2 : permL A 2 = d)
    (hs01 : negL A 0 = negL A 1) (hs32 : negL A 3 = negL A 2) :
    Frame n a b c d (A.map (NL.toPG n)) (A'.map (NL.toPG n)) := by
  have v : ∀ j < 4, ((ix n j : Fin (2 ^ n)) : ℕ) = j := fun j hj => ix_val (by omega)
  have P := fun j => (spW_NL hbd (ix n j)).1
  have S := fun j => (spW_NL hbd (ix n j)).2
  refine ⟨HP_NL hbd hpr, HP_NL hbd' hpr', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← List.map_append]
    exact spW_one_NL (fun x hx => (List.mem_append.1 hx).elim (hbd x) (hbd' x)) hinv
  · rw [P, v 0 (by norm_num), h0]
  · rw [P, v 1 (by norm_num), h1]
  · rw [P, v 3 (by norm_num), h3]
  · rw [P, v 2 (by norm_num), h2]
  · rw [S, S, v 0 (by norm_num), v 1 (by norm_num), hs01]
  · rw [S, S, v 3 (by norm_num), v 2 (by norm_num), hs32]

/-! ## Telescopes -/

theorem tau_swN (x i v : ℕ) : tau (if x ≠ i then 1 else 0) x i v = swN x i v := by
  by_cases h : x = i
  · subst h
    have e : (if x ≠ x then 1 else 0) = 0 := by simp
    rw [e]; unfold tau swN; split_ifs <;> omega
  · have e : (if x ≠ i then 1 else 0) = 1 := by simp [h]
    rw [e]; rfl

theorem swN_swN (x i v : ℕ) : swN x i (swN x i v) = v := by
  unfold swN; split_ifs <;> omega

theorem swN_self (x v : ℕ) : swN x x v = v := by
  unfold swN; split_ifs <;> omega

theorem swN_right (x i : ℕ) : swN x i i = x := by
  unfold swN; split_ifs <;> omega

/-- `ρ_p`: the composite of the transpositions of a plan, the last pair acting first. -/
def rho : List (ℕ × ℕ) → ℕ → ℕ
  | [], v => v
  | (x, k) :: p, v => tau (if x ≠ rho p k then 1 else 0) x (rho p k) (rho p v)

theorem rho_cons (x k : ℕ) (p : List (ℕ × ℕ)) (v : ℕ) :
    rho ((x, k) :: p) v = swN x (rho p k) (rho p v) := tau_swN _ _ _

theorem rho_inj : ∀ p : List (ℕ × ℕ), Function.Injective (rho p)
  | [] => fun _ _ h => h
  | (x, k) :: p => fun u v h => by
    rw [rho_cons, rho_cons] at h
    exact rho_inj p (swN_inj _ _ h)

/-- A letter of a telescope: present when `e = 1`. -/
def telL (e m x i : ℕ) : List NL := if e = 1 then [.zx m x i] else []

theorem telL_map (e m x i : ℕ) :
    (telL e m x i).map (NL.toPG n) = if e = 1 then [Zx n m x i] else [] := by
  unfold telL; split_ifs <;> rfl

/-- The telescope of a plan, with signs on the images of `s`. -/
def telNL (s : ℕ) : List (ℕ × ℕ) → List NL
  | [] => []
  | (x, k) :: p => telL (if x ≠ rho p k then 1 else 0) (rho ((x, k) :: p) s) x (rho p k) ++ telNL s p

/-- Its inverse. -/
def telNL' (s : ℕ) : List (ℕ × ℕ) → List NL
  | [] => []
  | (x, k) :: p => telNL' s p ++ telL (if x ≠ rho p k then 1 else 0) (rho p s) x (rho p k)

theorem permL_telL (m x i w : ℕ) :
    permL (telL (if x ≠ i then 1 else 0) m x i) w = swN x i w := by
  by_cases h : x = i
  · subst h; simp [telL, permL, swN_self]
  · simp [telL, h, permL, NL.perm]

theorem negL_telL (m x i w : ℕ) :
    negL (telL (if x ≠ i then 1 else 0) m x i) w = (decide (x ≠ i) && decide (swN x i w = m)) := by
  by_cases h : x = i
  · subst h; simp [telL, negL]
  · simp only [telL, h, ne_eq, not_false_eq_true, if_true, negL, permL, id, NL.neg, decide_true,
      Bool.true_and]
    split_ifs <;> simp_all

theorem permL_telNL (s : ℕ) : ∀ (p : List (ℕ × ℕ)) (v : ℕ), permL (telNL s p) v = rho p v
  | [], _ => rfl
  | (x, k) :: p, v => by
    rw [telNL, permL_append, permL_telNL s p, permL_telL, rho_cons]

theorem negL_telNL (s : ℕ) : ∀ (p : List (ℕ × ℕ)) (v : ℕ), v ≠ s → negL (telNL s p) v = false
  | [], _, _ => rfl
  | (x, k) :: p, v, hv => by
    rw [telNL, negL_append, permL_telNL, negL_telNL s p v hv, negL_telL, rho_cons]
    have : swN x (rho p k) (rho p v) ≠ swN x (rho p k) (rho p s) := fun h =>
      hv (rho_inj p (swN_inj _ _ h))
    simp [this]

/-- The telescope and its inverse cancel. -/
theorem telNL_inv (s : ℕ) : ∀ (p : List (ℕ × ℕ)) (v : ℕ),
    permL (telNL s p ++ telNL' s p) v = v ∧ negL (telNL s p ++ telNL' s p) v = false
  | [], _ => ⟨rfl, rfl⟩
  | (x, k) :: p, v => by
    have ih := telNL_inv s p
    have e1 : telNL s ((x, k) :: p) ++ telNL' s ((x, k) :: p) =
        telL (if x ≠ rho p k then 1 else 0) (rho ((x, k) :: p) s) x (rho p k) ++
          ((telNL s p ++ telNL' s p) ++
            telL (if x ≠ rho p k then 1 else 0) (rho p s) x (rho p k)) := by
      simp [telNL, telNL']
    rw [e1]
    have hM : ∀ w, permL ((telNL s p ++ telNL' s p) ++
        telL (if x ≠ rho p k then 1 else 0) (rho p s) x (rho p k)) w = swN x (rho p k) w := by
      intro w; rw [permL_append, (ih _).1, permL_telL]
    have hN' : ∀ w, negL ((telNL s p ++ telNL' s p) ++
        telL (if x ≠ rho p k then 1 else 0) (rho p s) x (rho p k)) w =
        negL (telL (if x ≠ rho p k then 1 else 0) (rho p s) x (rho p k)) w := by
      intro w; rw [negL_append, (ih _).2]; exact Bool.false_xor _
    refine ⟨?_, ?_⟩
    · rw [permL_append, hM, permL_telL, swN_swN]
    · rw [negL_append, hM, hN', negL_telL, negL_telL, swN_swN, rho_cons]
      generalize rho p k = i
      generalize rho p s = r
      by_cases h : x = i
      · simp [h]
      · by_cases hv : swN x i v = r
        · have hv' : v = swN x i r := by rw [← hv, swN_swN]
          simp [h, hv', swN_swN]
        · have hv' : ¬ v = swN x i r := fun e' => hv (by rw [e', swN_swN])
          simp [h, hv, hv']

/-- Targets and numerals of a plan are distinct. -/
def PlanOk (p : List (ℕ × ℕ)) : Prop := (p.map Prod.fst).Nodup ∧ (p.map Prod.snd).Nodup

/-- `ρ_p` sends each numeral of the plan to its target. -/
theorem rho_mem : ∀ p : List (ℕ × ℕ), PlanOk p → ∀ x k, (x, k) ∈ p → rho p k = x
  | [], _, _, _, h => absurd h (List.not_mem_nil)
  | (y, j) :: p, hp, x, k, h => by
    have hp' : PlanOk p := ⟨(List.nodup_cons.1 hp.1).2, (List.nodup_cons.1 hp.2).2⟩
    rw [rho_cons]
    rcases List.mem_cons.1 h with e | h
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 e
      exact swN_right _ _
    · have hx := rho_mem p hp' x k h
      rw [hx]
      have hx1 : x ∈ p.map Prod.fst := List.mem_map.2 ⟨(x, k), h, rfl⟩
      have hk1 : k ∈ p.map Prod.snd := List.mem_map.2 ⟨(x, k), h, rfl⟩
      have hxy : x ≠ y := fun e => (List.nodup_cons.1 hp.1).1 (e ▸ hx1)
      have hkj : k ≠ j := fun e => (List.nodup_cons.1 hp.2).1 (e ▸ hk1)
      have hxi : x ≠ rho p j := fun e => hkj (rho_inj p (hx.trans e))
      unfold swN; rw [if_neg hxy, if_neg hxi]

/-- Bounds for a plan: targets and numerals below `N`. -/
def PlanBd (N : ℕ) (p : List (ℕ × ℕ)) : Prop := ∀ q ∈ p, q.1 < N ∧ q.2 < N

theorem swN_lt_of {N x i v : ℕ} (hx : x < N) (hi : i < N) (hv : v < N) : swN x i v < N := by
  unfold swN; split_ifs <;> assumption

theorem rho_lt {N : ℕ} : ∀ p : List (ℕ × ℕ), PlanBd N p → ∀ v < N, rho p v < N
  | [], _, _, hv => hv
  | (x, k) :: p, hp, v, hv => by
    have hp' : PlanBd N p := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    rw [rho_cons]
    exact swN_lt_of (hp (x, k) (by simp)).1 (rho_lt p hp' k (hp (x, k) (by simp)).2)
      (rho_lt p hp' v hv)

theorem telL_bd {e m x i : ℕ} (hm : m < 2 ^ n) (hx : x < 2 ^ n) (hi : i < 2 ^ n) :
    ∀ y ∈ telL e m x i, y.Bd n := by
  intro y hy; unfold telL at hy; split_ifs at hy
  · simp only [List.mem_singleton] at hy; subst hy; exact ⟨hm, hx, hi⟩
  · simp at hy

theorem telL_pr {m x i : ℕ} : ∀ y ∈ telL (if x ≠ i then 1 else 0) m x i, y.Pr := by
  intro y hy; unfold telL at hy
  by_cases h : x = i
  · simp [h] at hy
  · simp only [h, ne_eq, not_false_eq_true, if_true, List.mem_singleton] at hy
    subst hy; exact h

theorem telNL_bd {s : ℕ} (hs : s < 2 ^ n) : ∀ p : List (ℕ × ℕ), PlanBd (2 ^ n) p →
    (∀ y ∈ telNL s p, y.Bd n) ∧ (∀ y ∈ telNL' s p, y.Bd n)
  | [], _ => ⟨by simp [telNL], by simp [telNL']⟩
  | (x, k) :: p, hp => by
    have hp' : PlanBd (2 ^ n) p := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    obtain ⟨ih1, ih2⟩ := telNL_bd hs p hp'
    have hx := (hp (x, k) (by simp)).1
    have hi := rho_lt p hp' k (hp (x, k) (by simp)).2
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rcases List.mem_append.1 hy with hy | hy
      · exact telL_bd (rho_lt _ hp s hs) hx hi y hy
      · exact ih1 y hy
    · rcases List.mem_append.1 hy with hy | hy
      · exact ih2 y hy
      · exact telL_bd (rho_lt _ hp' s hs) hx hi y hy

theorem telNL_pr (s : ℕ) : ∀ p : List (ℕ × ℕ),
    (∀ y ∈ telNL s p, y.Pr) ∧ (∀ y ∈ telNL' s p, y.Pr)
  | [] => ⟨by simp [telNL], by simp [telNL']⟩
  | (x, k) :: p => by
    obtain ⟨ih1, ih2⟩ := telNL_pr s p
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rcases List.mem_append.1 hy with hy | hy
      · exact telL_pr y hy
      · exact ih1 y hy
    · rcases List.mem_append.1 hy with hy | hy
      · exact ih2 y hy
      · exact telL_pr y hy

/-- A telescope through `(a,0), (b,1), (c,3), (d,2)` with a spare numeral other
than `0, …, 3` is a frame for `(a, b, c, d)`. -/
theorem Frame.tel (hN : 4 ≤ 2 ^ n) {a b c d s : ℕ} {p : List (ℕ × ℕ)} (hok : PlanOk p)
    (hbd : PlanBd (2 ^ n) p) (hs : s < 2 ^ n) (hs4 : 4 ≤ s)
    (ha : (a, 0) ∈ p) (hb : (b, 1) ∈ p) (hc : (c, 3) ∈ p) (hd : (d, 2) ∈ p) :
    Frame n a b c d ((telNL s p).map (NL.toPG n)) ((telNL' s p).map (NL.toPG n)) := by
  obtain ⟨b1, b2⟩ := telNL_bd hs p hbd
  obtain ⟨r1, r2⟩ := telNL_pr s p
  refine Frame.ofNL hN b1 b2 r1 r2 (fun v _ => telNL_inv s p v) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [permL_telNL, rho_mem p hok a 0 ha]
  · rw [permL_telNL, rho_mem p hok b 1 hb]
  · rw [permL_telNL, rho_mem p hok c 3 hc]
  · rw [permL_telNL, rho_mem p hok d 2 hd]
  · rw [negL_telNL s p 0 (by omega), negL_telNL s p 1 (by omega)]
  · rw [negL_telNL s p 3 (by omega), negL_telNL s p 2 (by omega)]

/-! ## Definition E.1 and Equation (35) -/

/-- The plan of `Σ_{a,b,c,d}`. -/
def sigPlan (a b c d : ℕ) : List (ℕ × ℕ) := [(a, 0), (b, 1), (c, 3), (d, 2)]

theorem sigmaW_eq (a b c d : ℕ) :
    sigmaW n a b c d = ((telNL 4 (sigPlan a b c d)).map (NL.toPG n),
      (telNL' 4 (sigPlan a b c d)).map (NL.toPG n)) := by
  simp only [sigmaW, sigPlan, telNL, telNL', List.map_append, telL_map, rho, List.map_nil,
    List.append_nil, List.nil_append, List.append_assoc] <;> rfl

theorem sigPlan_ok {a b c d : ℕ} (h : Distinct4 a b c d) : PlanOk (sigPlan a b c d) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, by simp [sigPlan]⟩
  simp [sigPlan, h1, h2, h3, h4, h5, h6]

theorem sigPlan_bd (h8 : 8 ≤ 2 ^ n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) : PlanBd (2 ^ n) (sigPlan a b c d) := by
  intro q hq
  simp only [sigPlan, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> exact ⟨by assumption, by omega⟩

/-- `Σ_{a,b,c,d}, Σ'_{a,b,c,d}` is a frame for `(a, b, c, d)`. -/
theorem Frame.sigma (h8 : 8 ≤ 2 ^ n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (h : Distinct4 a b c d) :
    Frame n a b c d (sigmaW n a b c d).1 (sigmaW n a b c d).2 := by
  rw [sigmaW_eq]
  exact Frame.tel (by omega) (sigPlan_ok h) (sigPlan_bd h8 ha hb hc hd) (by omega) le_rfl
    (by simp [sigPlan]) (by simp [sigPlan]) (by simp [sigPlan]) (by simp [sigPlan])

/-- Equation (65): `H_[a,b]H_[c,d] ≈ Σ_{a,b,c,d} Λ Σ'_{a,b,c,d}` for every tuple
of distinct indices. -/
def E65 (n : ℕ) : Prop :=
  ∀ a b c d : ℕ, a < 2 ^ n → b < 2 ^ n → c < 2 ^ n → d < 2 ^ n → Distinct4 a b c d →
    D8 n [Hh n a b c d] ((sigmaW n a b c d).1 ++ Lam n :: (sigmaW n a b c d).2)

/-- Equation (35) is Equation (65) when the Gray codes have neither form. -/
theorem e65_of_35 {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) (h : Distinct4 a b c d) (hp : patt n a b c d = none) :
    D8 n [Hh n a b c d] ((sigmaW n a b c d).1 ++ Lam n :: (sigmaW n a b c d).2) :=
  (DR.ax (Fig8.r35 a b c d ha hb hc hd h hp)).trans (DR.rfl' (by simp))

/-- Equation (65), for any frame. -/
theorem hh_frame (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (h : Distinct4 a b c d) {A A' : List (PG (2 ^ n))}
    (hF : Frame n a b c d A A') : D8 n [Hh n a b c d] (A ++ Lam n :: A') :=
  (hE a b c d ha hb hc hd h).trans (frame_eq (by omega) (Frame.sigma h8 ha hb hc hd h) hF)

theorem Distinct4.swap {a b c d : ℕ} (h : Distinct4 a b c d) : Distinct4 c d a b := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h6, Ne.symm h2, Ne.symm h4, Ne.symm h3, Ne.symm h5, h1⟩

/-- Equation (66): `H_[a,b]H_[c,d] ≈ H_[c,d]H_[a,b]`. -/
theorem e66 (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) (h : Distinct4 a b c d) :
    D8 n [Hh n a b c d] [Hh n c d a b] :=
  (hE a b c d ha hb hc hd h).trans <|
    (frame_swap (by omega) (Frame.sigma h8 ha hb hc hd h) (Frame.sigma h8 hc hd ha hb h.swap)).trans
      (hE c d a b hc hd ha hb h.swap).symm

end QCert.RealCliffordCH.Sec8
