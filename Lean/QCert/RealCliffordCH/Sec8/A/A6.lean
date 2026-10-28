/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.6 and Corollary A.7

`Λ = H_[0,1]H_[3,2]`.  A list of letters passes `Λ` (`Pass`) when
`l Λ ≈ Λ l`.  Lemma A.6 characterizes the Hadamard-free words commuting
with `Λ` semantically: they are, up to Corollary A.5, the words
`((-1)_[0](-1)_[1])^α ((-1)_[3](-1)_[2])^β (X_[0,3]X_[1,2])^γ Q` with `Q` a
product of letters `(-1)_[a]X_[a,a+1]`, `a ≥ 4`, and these pass `Λ` by
Equations (38), (39) and (44).  We state it on signed permutations, so that
no real matrix enters: a Hadamard-free word passes `Λ` as soon as its
signed permutation fixes `0, 1, 3, 2` or sends them to `3, 2, 0, 1`, with
the same sign on `0` and `1` and on `3` and `2` (`CommL`), which is what a
signed permutation commuting with `Λ` does (`A6`).

The word `Q` is found in the normal form of Lemma A.4: when the signed
permutation fixes `0, …, 3` with sign `+`, every run of the normal form is
made of letters `σ_j`, `j ≥ 4` (`pidx_ge4`), and its sign part
`∏ (-1)_[0](-1)_[x]` has an even number of factors, all with `x ≥ 4`, which
pair up into signs `(-1)_[x](-1)_[y]`, `x, y ≥ 4` (`pass_fix`).

Corollary A.7 (`A7`): if `A A'` and `B B'` are the identity and `B' A`
satisfies `CommL`, then `A Λ A' ≈ B Λ B'`.
-/
import QCert.RealCliffordCH.Sec8.A.A5

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- A proper Hadamard-free list. -/
def HP {N : ℕ} (l : List (PG N)) : Prop := ∀ x ∈ l, x.HF ∧ x.Proper

theorem HP.append {N : ℕ} {l l' : List (PG N)} (h : HP l) (h' : HP l') : HP (l ++ l') :=
  fun x hx => (List.mem_append.1 hx).elim (h x) (h' x)

theorem HP.nil {N : ℕ} : HP ([] : List (PG N)) := fun _ h => absurd h (List.not_mem_nil)

theorem pSem_HP {l : List (PG (2 ^ n))} (hl : HP l) :
    pSem (wordOf l) = spMat (spW (wordOf l)) :=
  pWord_eq_spMat _ _ (fun x hx => (hl x (by simpa [wordOf] using hx)).1)
    (fun x hx => (hl x (by simpa [wordOf] using hx)).2)

/-- Corollary A.5, from the equality of the signed permutations. -/
theorem A5s (hN : 4 ≤ 2 ^ n) {l l' : List (PG (2 ^ n))} (hl : HP l) (hl' : HP l')
    (h : spW (wordOf l) = spW (wordOf l')) : D8 n l l' :=
  A5 hN hl hl' (by rw [pSem_HP hl, pSem_HP hl', h])

theorem spW_nil : spW (wordOf ([] : List (PG (2 ^ n)))) = 1 := map_one _

/-! ## Passing `Λ` -/

/-- `Λ = H_[0,1] H_[3,2]`. -/
abbrev Lam (n : ℕ) : PG (2 ^ n) := Hh n 0 1 3 2

/-- `l` passes `Λ`: `l Λ ≈ Λ l`. -/
def Pass (n : ℕ) (l : List (PG (2 ^ n))) : Prop := D8 n (l ++ [Lam n]) (Lam n :: l)

theorem Pass.nil : Pass n [] := DR.refl _

theorem Pass.append {a b : List (PG (2 ^ n))} (ha : Pass n a) (hb : Pass n b) :
    Pass n (a ++ b) :=
  (DR.rfl' (List.append_assoc a b [Lam n])).trans <| (DR.left a hb).trans <|
    (DR.rfl' (by simp)).trans <| (DR.right b ha).trans (DR.rfl' (by simp))

theorem Pass.congr {l l' : List (PG (2 ^ n))} (h : D8 n l l') (hl : Pass n l) : Pass n l' :=
  (DR.right [Lam n] h.symm).trans (hl.trans (DR.cons (Lam n) h))

/-- Equation (38). -/
theorem pass_sg {j : ℕ} (h4 : 4 ≤ j) (hj : j + 1 < 2 ^ n) : Pass n [sg n j] :=
  DR.ax (Fig8.r38 j h4 hj)

/-- Equation (39). -/
theorem pass_zz01 : Pass n [Zz n 0 1] := DR.ax (Fig8.r39 (n := n))

/-- Equation (44). -/
theorem pass_xx : Pass n [Xx n 0 3 1 2] := DR.ax (Fig8.r44 (n := n))

theorem pass_sgs : ∀ js : List ℕ, (∀ j ∈ js, 4 ≤ j ∧ j + 1 < 2 ^ n) → Pass n (js.map (sg n))
  | [], _ => Pass.nil
  | j :: js, h => by
    have h1 := h j (by simp)
    exact Pass.append (pass_sg h1.1 h1.2)
      (pass_sgs js fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- `(-1)_[a](-1)_[a+k]` passes `Λ`, `a ≥ 4`. -/
theorem pass_zz_up : ∀ (k a : ℕ), 4 ≤ a → a + k < 2 ^ n → Pass n [Zz n a (a + k)]
  | 0, a, _, hk => Pass.congr (DH.toD8 (e20 n (a := a) (by omega))).symm Pass.nil
  | k + 1, a, h4, hk => by
    have ih := pass_zz_up k (a + 1) (by omega) (by omega)
    have h23 : Pass n [Zz n a (a + 1)] :=
      Pass.congr (DH.toD8 (e23 n (a := a) (by omega))).symm
        (Pass.append (pass_sg h4 (by omega)) (pass_sg h4 (by omega)))
    have h22 : D8 n [Zz n a (a + 1), Zz n (a + 1) (a + 1 + k)] [Zz n a (a + (k + 1))] := by
      rw [show a + (k + 1) = a + 1 + k by omega]
      exact DH.toD8 (e22 n (by omega) (by omega) (by omega))
    exact Pass.congr h22 (Pass.append h23 ih)

/-- `(-1)_[a](-1)_[c]` passes `Λ`, `a, c ≥ 4`. -/
theorem pass_zz4 {a c : ℕ} (ha : 4 ≤ a) (hc : 4 ≤ c) (ha' : a < 2 ^ n) (hc' : c < 2 ^ n) :
    Pass n [Zz n a c] := by
  rcases le_total a c with h | h
  · have := pass_zz_up (n := n) (c - a) a ha (by omega)
    rwa [show a + (c - a) = c by omega] at this
  · have := pass_zz_up (n := n) (a - c) c hc (by omega)
    rw [show c + (a - c) = a by omega] at this
    exact Pass.congr (DH.toD8 (e21 n hc' ha')) this

theorem Pass.spW (hN : 4 ≤ 2 ^ n) {l l' : List (PG (2 ^ n))} (hl : HP l) (hl' : HP l')
    (h : spW (wordOf l) = spW (wordOf l')) (hp : Pass n l) : Pass n l' :=
  Pass.congr (A5s hN hl hl' h) hp

/-! ## Signed permutations fixing `0, …, 3` -/

theorem permL_sgs_lo {x : ℕ} : ∀ js : List ℕ, (∀ j ∈ js, x < j) → permL (js.map sgNL) x = x
  | [], _ => rfl
  | j :: js, h => by
    have hj := h j (by simp)
    have ih := permL_sgs_lo js fun i hi => h i (List.mem_cons_of_mem _ hi)
    show swN j (j + 1) (permL (js.map sgNL) x) = x
    rw [ih, swN, if_neg (by omega), if_neg (by omega)]

theorem negL_sgs_lo {x : ℕ} : ∀ js : List ℕ, (∀ j ∈ js, x < j) → negL (js.map sgNL) x = false
  | [], _ => rfl
  | j :: js, h => by
    have hj := h j (by simp)
    have h' : ∀ i ∈ js, x < i := fun i hi => h i (List.mem_cons_of_mem _ hi)
    show (if (sgNL j).neg (permL (js.map sgNL) x) then !negL (js.map sgNL) x
      else negL (js.map sgNL) x) = false
    rw [permL_sgs_lo js h', negL_sgs_lo js h']
    simp [sgNL, NL.neg, swN, show x ≠ j by omega, show x ≠ j + 1 by omega]

/-- If the permutation part, preceded by letters `σ_t`, `t ≥ 4`, fixes `0, …, 3`,
its letters are all `σ_j` with `j ≥ 4`. -/
theorem pidx_ge4 {d : ℕ → ℕ} : ∀ (m : ℕ) (ts : List ℕ), Code d m → (∀ t ∈ ts, 4 ≤ t) →
    (∀ j < 4, permL (ts.map sgNL ++ PNL d m) j = j) → ∀ j ∈ pidx d m, 4 ≤ j
  | 0, _, _, _, _, j, hj => by simp [pidx] at hj
  | m + 1, ts, hd, hts, hfix, j, hj => by
    have hdm := hd m (by omega)
    have hsplit : ts.map sgNL ++ PNL d (m + 1) =
        (ts.map sgNL ++ (List.range' (d m) (m - d m)).map sgNL) ++ PNL d m := by
      simp [PNL, pidx]
    have key : d m = m ∨ 4 ≤ d m := by
      by_contra hc
      push Not at hc
      obtain ⟨hne, hlt⟩ := hc
      have hRP : ∀ x < 4, permL ((List.range' (d m) (m - d m)).map sgNL) (permL (PNL d m) x) = x := by
        intro x hx
        have h1 := hfix x hx
        rw [hsplit, permL_append, permL_append] at h1
        apply permL_sgs_inj ts
        rw [h1, permL_sgs_lo ts (fun t ht => by have := hts t ht; omega)]
      have hPm : permL (PNL d m) m = m :=
        permL_sgs_fix (pidx d m) (pidx_lt fun k hk => hd k (by omega))
      have hRm : permL ((List.range' (d m) (m - d m)).map sgNL) m = d m := by
        have := permL_run (d m) (m - d m)
        rwa [show d m + (m - d m) = m by omega] at this
      have e : permL ((List.range' (d m) (m - d m)).map sgNL) (permL (PNL d m) (d m)) =
          permL ((List.range' (d m) (m - d m)).map sgNL) (permL (PNL d m) m) := by
        rw [hRP (d m) hlt, hPm, hRm]
      have := permL_sgs_inj _ (permL_sgs_inj _ e)
      omega
    have hts' : ∀ t ∈ ts ++ List.range' (d m) (m - d m), 4 ≤ t := by
      intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · exact hts t ht
      · simp only [List.mem_range'] at ht
        rcases key with h | h <;> omega
    have hfix' : ∀ j < 4, permL ((ts ++ List.range' (d m) (m - d m)).map sgNL ++ PNL d m) j = j := by
      intro j hj
      rw [List.map_append, ← hsplit]; exact hfix j hj
    simp only [pidx, List.mem_append, List.mem_range'] at hj
    rcases hj with ⟨i, hi, rfl⟩ | hj
    · rcases key with h | h <;> omega
    · exact pidx_ge4 m _ (fun k hk => hd k (by omega)) hts' hfix' j hj

theorem SWl_eq_filter (b : ℕ → Bool) : ∀ xs : List ℕ,
    SWl n b xs = (xs.filter b).map (Zz n 0 ·)
  | [] => rfl
  | x :: xs => by
    rw [SWl_cons, SWl_eq_filter b xs, List.filter_cons]
    cases b x <;> simp

theorem negL_SWL_zero (b : ℕ → Bool) : ∀ xs : List ℕ, (∀ x ∈ xs, 1 ≤ x) →
    negL (SWL b xs) 0 = decide ((xs.filter b).length % 2 = 1)
  | [], _ => rfl
  | x :: xs, h => by
    have ih := negL_SWL_zero b xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x (by simp)
    have e : SWL b (x :: xs) = (if b x then [NL.zz 0 x] else []) ++ SWL b xs := by
      simp [SWL]
    rw [e, negL_append, permL_SWL, ih, List.filter_cons]
    cases hb : b x
    · simp [negL]
    · have h0 : (0 : ℕ) ≠ x := by omega
      simp only [if_true, negL, permL, NL.neg, id, h0, if_false, List.length_cons]
      rcases Nat.mod_two_eq_zero_or_one (List.filter b xs).length with h2 | h2 <;>
        simp [h2, Nat.add_mod]

/-- An even number of signs `(-1)_[0](-1)_[y]`, `y ≥ 4`, passes `Λ`. -/
theorem pass_pairs : ∀ ys : List ℕ, (∀ y ∈ ys, 4 ≤ y ∧ y < 2 ^ n) → ys.length % 2 = 0 →
    Pass n (ys.map (Zz n 0 ·))
  | [], _, _ => Pass.nil
  | [_], _, h => absurd h (by simp)
  | y1 :: y2 :: ys, hy, h => by
    have h1 := hy y1 (by simp)
    have h2 := hy y2 (by simp)
    have hrest := pass_pairs ys (fun y hy' => hy y (by simp [hy'])) (by simp at h; omega)
    have hd : D8 n [Zz n y1 y2] [Zz n 0 y1, Zz n 0 y2] :=
      DH.toD8 (zz_split (Nat.two_pow_pos n) h1.2 h2.2)
    exact Pass.append (a := [Zz n 0 y1, Zz n 0 y2]) (Pass.congr hd (pass_zz4 h1.1 h2.1 h1.2 h2.2))
      hrest

/-- A proper Hadamard-free word whose signed permutation fixes `0, …, 3`
with sign `+` passes `Λ`. -/
theorem pass_fix (hN : 4 ≤ 2 ^ n) {l : List (PG (2 ^ n))} (hl : HP l)
    (hfix : ∀ j < 4, ((spW (wordOf l)).perm (ix n j) : ℕ) = j ∧
      (spW (wordOf l)).neg (ix n j) = false) : Pass n l := by
  obtain ⟨b, d, hd, h1⟩ := nf_of hN hl
  have hs := DH.spW h1
  refine Pass.congr (DH.toD8 h1).symm ?_
  have hlt : ∀ j < 4, j < 2 ^ n := fun j hj => by omega
  have hbd : ∀ x ∈ SWL b (sidx n) ++ PNL d (2 ^ n), x.Bd n := fun x hx =>
    (List.mem_append.1 hx).elim (SWL_bd b x) (PNL_bd hd x)
  have heq : NFW n b d = (SWL b (sidx n) ++ PNL d (2 ^ n)).map (NL.toPG n) := by
    rw [NFW, SWl_eq_map, PN_eq_map, List.map_append]
  have hNL : ∀ j < 4, permL (SWL b (sidx n) ++ PNL d (2 ^ n)) j = j ∧
      negL (SWL b (sidx n) ++ PNL d (2 ^ n)) j = false := by
    intro j hj
    obtain ⟨e1, e2⟩ := spW_NL hbd (ix n j)
    rw [← heq, ← hs, (hfix j hj).1, ix_val (hlt j hj)] at e1
    rw [← heq, ← hs, (hfix j hj).2, ix_val (hlt j hj)] at e2
    exact ⟨e1.symm, e2.symm⟩
  have hperm : ∀ j < 4, permL (PNL d (2 ^ n)) j = j := fun j hj => by
    have := (hNL j hj).1; rwa [permL_append, permL_SWL] at this
  have hge := pidx_ge4 (2 ^ n) [] hd (by simp) (by simpa using hperm)
  have hnegP : ∀ j < 4, negL (PNL d (2 ^ n)) j = false := fun j hj =>
    negL_sgs_lo _ fun i hi => by have := hge i hi; omega
  have hnegS : ∀ j < 4, negL (SWL b (sidx n)) j = false := fun j hj => by
    have := (hNL j hj).2
    rw [negL_append, hperm j hj, hnegP j hj] at this
    simpa using this
  have hb : ∀ x, 1 ≤ x → x < 4 → b x = false := fun x h1 h4 => by
    have := hnegS x h4
    rw [negL_SWL b h1 _ sidx_nodup] at this
    simpa [mem_sidx h1 (hlt x h4)] using this
  have hpar : ((sidx n).filter b).length % 2 = 0 := by
    have := hnegS 0 (by norm_num)
    rw [negL_SWL_zero b _ (fun x hx => by simp only [sidx, List.mem_range'] at hx; omega)] at this
    simp at this; omega
  have hS : Pass n (SWl n b (sidx n)) := by
    rw [SWl_eq_filter]
    refine pass_pairs _ (fun y hy => ?_) hpar
    rw [List.mem_filter] at hy
    have h1 : 1 ≤ y := by have := hy.1; simp only [sidx, List.mem_range'] at this; omega
    refine ⟨?_, sidx_lt y hy.1⟩
    by_contra h4
    have := hb y h1 (by omega)
    simp [this] at hy
  have hP : Pass n (PN n d (2 ^ n)) :=
    pass_sgs _ fun j hj => ⟨hge j hj, pidx_lt hd j hj⟩
  exact Pass.append hS hP

/-! ## Lemma A.6 -/

/-- A signed permutation commuting with `Λ`: it fixes `0, 1, 3, 2` or sends them
to `3, 2, 0, 1`, with equal signs on `0, 1` and on `3, 2`. -/
def CommL (n : ℕ) (M : SP (2 ^ n)) : Prop :=
  ((((M.perm (ix n 0) : ℕ) = 0 ∧ (M.perm (ix n 1) : ℕ) = 1 ∧ (M.perm (ix n 3) : ℕ) = 3 ∧
      (M.perm (ix n 2) : ℕ) = 2) ∨
    ((M.perm (ix n 0) : ℕ) = 3 ∧ (M.perm (ix n 1) : ℕ) = 2 ∧ (M.perm (ix n 3) : ℕ) = 0 ∧
      (M.perm (ix n 2) : ℕ) = 1)) ∧
    M.neg (ix n 0) = M.neg (ix n 1) ∧ M.neg (ix n 3) = M.neg (ix n 2))

/-- The correction `(X_[0,3]X_[1,2])^γ ((-1)_[0](-1)_[1])^α ((-1)_[3](-1)_[2])^β`. -/
def corrNL (γ α β : Bool) : List NL :=
  (if γ then [.xx 0 3 1 2] else []) ++ (if α then [.zz 0 1] else []) ++
    (if β then [.zz 3 2] else [])

theorem corrNL_bd (hN : 4 ≤ 2 ^ n) (γ α β : Bool) : ∀ x ∈ corrNL γ α β, x.Bd n := by
  intro x hx
  cases γ <;> cases α <;> cases β <;>
    simp only [corrNL, if_true, if_false, Bool.false_eq_true, List.nil_append, List.append_nil,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl <;> simp only [NL.Bd] <;> omega

theorem corrNL_HP (hN : 4 ≤ 2 ^ n) (γ α β : Bool) : HP ((corrNL γ α β).map (NL.toPG n)) := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hb := corrNL_bd hN γ α β y hy
  cases γ <;> cases α <;> cases β <;>
    simp only [corrNL, if_true, if_false, Bool.false_eq_true, List.nil_append, List.append_nil,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hy <;>
    rcases hy with rfl | rfl | rfl <;>
    simp only [NL.toPG, Zz, Xx, PG.HF, PG.Proper, true_and, ne_eq, Fin.ext_iff,
      ix_val (show (0 : ℕ) < 2 ^ n by omega), ix_val (show (1 : ℕ) < 2 ^ n by omega),
      ix_val (show (2 : ℕ) < 2 ^ n by omega), ix_val (show (3 : ℕ) < 2 ^ n by omega)] <;>
    decide

/-- `(-1)_[3](-1)_[2] ≈ X_[0,3]X_[1,2] (-1)_[0](-1)_[1] X_[0,3]X_[1,2]`, so it passes `Λ`. -/
theorem pass_zz32 (hN : 4 ≤ 2 ^ n) : Pass n [Zz n 3 2] := by
  have hbd : ∀ x ∈ [NL.xx 0 3 1 2, .zz 0 1, .xx 0 3 1 2], x.Bd n := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp only [NL.Bd] <;> omega
  have hbd' : ∀ x ∈ [NL.zz 3 2], x.Bd n := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp only [NL.Bd]; omega
  have hs := spW_eq_of_NL hbd hbd' (fun j hj => by
    by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> by_cases h2 : j = 2 <;>
      by_cases h3 : j = 3 <;> nl_eval)
  have hHP := corrNL_HP hN true true false
  have hHP' := corrNL_HP hN false false true
  have hp : Pass n [Xx n 0 3 1 2, Zz n 0 1, Xx n 0 3 1 2] :=
    Pass.append (a := [Xx n 0 3 1 2]) pass_xx (Pass.append (a := [Zz n 0 1]) pass_zz01 pass_xx)
  refine Pass.spW hN ?_ ?_ hs hp
  · intro x hx; simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hHP _ (by simp [corrNL, NL.toPG])
    · exact hHP _ (by simp [corrNL, NL.toPG])
    · exact hHP _ (by simp [corrNL, NL.toPG])
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; exact hHP' _ (by simp [corrNL, NL.toPG])

theorem pass_corr (hN : 4 ≤ 2 ^ n) (γ α β : Bool) :
    Pass n ((corrNL γ α β).reverse.map (NL.toPG n)) := by
  have p1 : Pass n ((if γ then [NL.xx 0 3 1 2] else []).map (NL.toPG n)) := by
    cases γ
    · exact Pass.nil
    · exact pass_xx
  have p2 : Pass n ((if α then [NL.zz 0 1] else []).map (NL.toPG n)) := by
    cases α
    · exact Pass.nil
    · exact pass_zz01
  have p3 : Pass n ((if β then [NL.zz 3 2] else []).map (NL.toPG n)) := by
    cases β
    · exact Pass.nil
    · exact pass_zz32 hN
  have e : (corrNL γ α β).reverse.map (NL.toPG n) =
      (if β then [NL.zz 3 2] else []).map (NL.toPG n) ++
        (if α then [NL.zz 0 1] else []).map (NL.toPG n) ++
          (if γ then [NL.xx 0 3 1 2] else []).map (NL.toPG n) := by
    cases γ <;> cases α <;> cases β <;> rfl
  rw [e]
  exact Pass.append (Pass.append p3 p2) p1

/-- An `NL` letter that is its own inverse. -/
def NL.Inv (x : NL) : Prop := ∀ v, permL [x, x] v = v ∧ negL [x, x] v = false

theorem permL_rev_inv : ∀ L : List NL, (∀ x ∈ L, x.Inv) →
    ∀ v, permL (L.reverse ++ L) v = v ∧ negL (L.reverse ++ L) v = false
  | [], _, _ => ⟨rfl, rfl⟩
  | x :: L, h, v => by
    have ih := permL_rev_inv L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    have e : (x :: L).reverse ++ x :: L = L.reverse ++ ([x, x] ++ L) := by simp
    rw [e]
    have hp : permL ([x, x] ++ L) v = permL L v := by rw [permL_append, (hx _).1]
    have hn : negL ([x, x] ++ L) v = negL L v := by
      rw [negL_append, (hx _).2]; exact Bool.false_xor _
    constructor
    · rw [permL_append, hp, ← permL_append]; exact (ih v).1
    · rw [negL_append, hp, hn, ← negL_append]; exact (ih v).2

theorem NL.inv_zz (a c : ℕ) : (NL.zz a c).Inv := fun v => by
  refine ⟨rfl, ?_⟩
  show (if (NL.zz a c).neg v then !(if (NL.zz a c).neg v then !false else false)
    else (if (NL.zz a c).neg v then !false else false)) = false
  cases (NL.zz a c).neg v <;> rfl

theorem NL.inv_xx0312 : (NL.xx 0 3 1 2).Inv := fun v => by
  refine ⟨?_, rfl⟩
  show swN 0 3 (swN 1 2 (swN 0 3 (swN 1 2 v))) = v
  simp only [swN]; split_ifs <;> first | omega | contradiction

theorem corrNL_rev (hN : 4 ≤ 2 ^ n) (γ α β : Bool) :
    spW (wordOf (((corrNL γ α β).reverse ++ corrNL γ α β).map (NL.toPG n))) =
      spW (wordOf (([] : List NL).map (NL.toPG n))) := by
  have hbd := corrNL_bd (n := n) hN γ α β
  have hinv : ∀ x ∈ corrNL γ α β, x.Inv := by
    intro x hx
    cases γ <;> cases α <;> cases β <;>
      simp only [corrNL, if_true, if_false, Bool.false_eq_true, List.nil_append, List.append_nil,
        List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;>
      first | exact NL.inv_zz _ _ | exact NL.inv_xx0312
  refine spW_eq_of_NL (fun x hx => (List.mem_append.1 hx).elim
    (fun h => hbd x (List.mem_reverse.1 h)) (hbd x)) (by simp) (fun j _ => ?_)
  simpa [permL, negL] using permL_rev_inv _ hinv j

/-- The values of the correction on `0, …, 3`. -/
theorem corrNL_vals (γ α β : Bool) (v : ℕ) (hv : v < 4) :
    permL (corrNL γ α β) v = (if γ then swN 0 3 (swN 1 2 v) else v) ∧
      negL (corrNL γ α β) v =
        xor (α && decide (v = 0 ∨ v = 1)) (β && decide (v = 3 ∨ v = 2)) := by
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> cases γ <;> cases α <;> cases β <;> decide

/-- **Lemma A.6**: a proper Hadamard-free word whose signed permutation
commutes with `Λ` passes `Λ`. -/
theorem A6 (hN : 4 ≤ 2 ^ n) {l : List (PG (2 ^ n))} (hl : HP l) (hc : CommL n (spW (wordOf l))) :
    Pass n l := by
  set M := spW (wordOf l) with hM
  obtain ⟨hp, hn01, hn32⟩ := hc
  have hlt : ∀ j < 4, j < 2 ^ n := fun j hj => by omega
  -- the correction `C`, chosen from the case of `CommL`
  obtain ⟨γ, α, β, hval⟩ : ∃ γ α β : Bool, ∀ j < 4,
      ((M.perm (ix n j) : ℕ) < 4) ∧
      permL (corrNL γ α β) (M.perm (ix n j)) = j ∧
      xor (negL (corrNL γ α β) (M.perm (ix n j))) (M.neg (ix n j)) = false := by
    rcases hp with ⟨p0, p1, p3, p2⟩ | ⟨p0, p1, p3, p2⟩
    · refine ⟨false, M.neg (ix n 0), M.neg (ix n 3), fun j hj => ?_⟩
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · rw [p0]; refine ⟨by norm_num, ?_, ?_⟩ <;>
          simp [(corrNL_vals _ _ _ 0 (by norm_num)).1, (corrNL_vals _ _ _ 0 (by norm_num)).2]
      · rw [p1]; refine ⟨by norm_num, ?_, ?_⟩ <;>
          simp [(corrNL_vals _ _ _ 1 (by norm_num)).1, (corrNL_vals _ _ _ 1 (by norm_num)).2, hn01]
      · rw [p2]; refine ⟨by norm_num, ?_, ?_⟩ <;>
          simp [(corrNL_vals _ _ _ 2 (by norm_num)).1, (corrNL_vals _ _ _ 2 (by norm_num)).2, hn32]
      · rw [p3]; refine ⟨by norm_num, ?_, ?_⟩ <;>
          simp [(corrNL_vals _ _ _ 3 (by norm_num)).1, (corrNL_vals _ _ _ 3 (by norm_num)).2]
    · refine ⟨true, M.neg (ix n 3), M.neg (ix n 0), fun j hj => ?_⟩
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · rw [p0]; refine ⟨by norm_num, ?_, ?_⟩ <;>
          simp [(corrNL_vals _ _ _ 3 (by norm_num)).1, (corrNL_vals _ _ _ 3 (by norm_num)).2, swN]
      · rw [p1]; refine ⟨by norm_num, ?_, ?_⟩ <;>
          simp [(corrNL_vals _ _ _ 2 (by norm_num)).1, (corrNL_vals _ _ _ 2 (by norm_num)).2, swN,
            hn01]
      · rw [p2]; refine ⟨by norm_num, ?_, ?_⟩ <;>
          simp [(corrNL_vals _ _ _ 1 (by norm_num)).1, (corrNL_vals _ _ _ 1 (by norm_num)).2, swN,
            hn32]
      · rw [p3]; refine ⟨by norm_num, ?_, ?_⟩ <;>
          simp [(corrNL_vals _ _ _ 0 (by norm_num)).1, (corrNL_vals _ _ _ 0 (by norm_num)).2, swN]
  set C := (corrNL γ α β).map (NL.toPG n)
  have hC : HP C := corrNL_HP hN γ α β
  have hCr : HP ((corrNL γ α β).reverse.map (NL.toPG n)) := fun x hx =>
    hC x (by rw [List.mem_map] at hx ⊢; obtain ⟨y, hy, e⟩ := hx; exact ⟨y, List.mem_reverse.1 hy, e⟩)
  have hbd := corrNL_bd hN γ α β
  -- `C l` fixes `0, …, 3` with sign `+`
  have hfix : ∀ j < 4, ((spW (wordOf (C ++ l))).perm (ix n j) : ℕ) = j ∧
      (spW (wordOf (C ++ l))).neg (ix n j) = false := by
    intro j hj
    obtain ⟨hv, e1, e2⟩ := hval j hj
    have hfin : M.perm (ix n j) = ix n (M.perm (ix n j)) := Fin.ext (ix_val (by omega)).symm
    rw [spW_wordOf_append, SP.mul_perm, SP.mul_neg, ← hM, hfin]
    obtain ⟨f1, f2⟩ := spW_NL hbd (ix n (M.perm (ix n j)))
    rw [ix_val (by omega)] at f1 f2
    exact ⟨f1.trans e1, by rw [f2]; exact e2⟩
  have hCl : Pass n (C ++ l) := pass_fix hN (hC.append hl) hfix
  have hCCl : Pass n ((corrNL γ α β).reverse.map (NL.toPG n) ++ (C ++ l)) :=
    Pass.append (pass_corr hN γ α β) hCl
  refine Pass.spW hN (hCr.append (hC.append hl)) hl ?_ hCCl
  rw [← List.append_assoc, spW_wordOf_append, ← List.map_append, corrNL_rev hN γ α β]
  simp [spW_nil]

/-! ## Corollary A.7 -/

/-- **Corollary A.7**: if `A A'` and `B B'` are the identity and `B' A` commutes
with `Λ`, then `A Λ A' ≈ B Λ B'`. -/
theorem A7 (hN : 4 ≤ 2 ^ n) {A A' B B' : List (PG (2 ^ n))} (hA : HP A) (hA' : HP A')
    (hB : HP B) (hB' : HP B') (h1 : spW (wordOf (A ++ A')) = 1)
    (h2 : spW (wordOf (B ++ B')) = 1) (hc : CommL n (spW (wordOf (B' ++ A)))) :
    D8 n (A ++ Lam n :: A') (B ++ Lam n :: B') := by
  have e1 : D8 n [] (B ++ B') := A5s hN HP.nil (hB.append hB') (by rw [spW_nil, h2])
  have e2 : D8 n (A ++ A') [] := A5s hN (hA.append hA') HP.nil (by rw [spW_nil, h1])
  have hp := A6 hN (hB'.append hA) hc
  exact (DR.right (A ++ Lam n :: A') e1).trans <|
    (DR.rfl' (by simp)).trans <| (DR.ctx B A' hp).trans <|
    (DR.rfl' (by simp)).trans <| (DR.left (B ++ Lam n :: B') e2).trans (DR.rfl' (by simp))

end QCert.RealCliffordCH.Sec8
