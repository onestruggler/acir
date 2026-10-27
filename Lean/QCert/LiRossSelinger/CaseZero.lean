/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20 at `k = 0`

At `k = 0` the pivot column is `±e_b` with `b ≤ j` (`ucol b t`, the sign
`-1` when `t`), and the syllable is `X_[b,j] (−1)_[b]^t` for `b < j`, and
`(−1)_[j]` for `b = j` (`syll_ucol_lt`, `syll_ucol_eq`).  Subcases 1.1
(`squareZ_X`), 2.1 (`squareZ_N`) and 3.1 (`squareZ_K`): a basic generator
moves `±e_b` to a column of the same kind, and the square is closed by at
most one generator.  For `K_[0,1,2,3]` with `b ≤ 3` the level goes up
(Subcases 3.1.1–3.1.4 are retrograde), which the hypothesis excludes.
-/
import QCert.LiRossSelinger.CaseN

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-- The column `±e_b` (`-` when `t`). -/
noncomputable def ucol (b : Fin n) (t : Bool) : Fin n → ℝ :=
  fun r => if r = b then (if t then -1 else 1) else 0

/-- The sign letter of a `k = 0` syllable. -/
def negw (t : Bool) (b : Fin n) : List (Gen n) := if t then [Gen.neg b] else []

theorem isCol_ucol (b : Fin n) (t : Bool) :
    IsCol (ucol b t) 0 (fun r => if r = b then (if t then -1 else 1) else 0) := by
  intro r; simp only [ucol, pow_zero, one_mul]; split_ifs <;> simp

theorem lde_ucol {V : O_ZHalf n} {b : Fin n} {t : Bool} (hc : pcol V = ucol b t) : lde V = 0 :=
  Nat.le_zero.1 (lde_le V (hc ▸ (isCol_ucol b t).intAt))

theorem ucol_ne {b : Fin n} {t : Bool} : ucol b t b ≠ 0 := by
  simp only [ucol, if_pos rfl]; cases t <;> norm_num

theorem choose_ucol {V : O_ZHalf n} {b : Fin n} {t : Bool} (hc : pcol V = ucol b t)
    (hex : ∃ a, pcol V a ≠ 0) : hex.choose = b := by
  by_contra h
  apply hex.choose_spec
  rw [congrFun hc hex.choose]
  simp [ucol, h]

theorem syll_ucol_lt (V : O_ZHalf n) (hV : 0 < pivotJ V) {b p : Fin n} {t : Bool}
    (hp : pidx V hV = p) (hc : pcol V = ucol b t) (hbp : b < p) :
    syll V = Gen.x b p hbp :: negw t b := by
  have hex : ∃ a, pcol V a ≠ 0 := ⟨b, by rw [hc]; exact ucol_ne⟩
  have hch := choose_ucol hc hex
  subst hp
  unfold syll
  rw [dif_pos hV, if_pos (lde_ucol hc), dif_pos hex]
  simp only [hch]
  rw [dif_pos hbp, congrFun hc b]
  cases t <;> simp [ucol, negw]

theorem syll_ucol_eq (V : O_ZHalf n) (hV : 0 < pivotJ V) {p : Fin n} {t : Bool}
    (hp : pidx V hV = p) (hc : pcol V = ucol p t) : syll V = [Gen.neg p] := by
  have hex : ∃ a, pcol V a ≠ 0 := ⟨p, by rw [hc]; exact ucol_ne⟩
  have hch := choose_ucol hc hex
  subst hp
  unfold syll
  rw [dif_pos hV, if_pos (lde_ucol hc), dif_pos hex]
  simp only [hch]
  rw [dif_neg (lt_irrefl _)]

/-- The pivot column of a state at `k = 0`. -/
theorem col_zero {s : O_ZHalf n} (hs : s ≠ 1) (hk : lde s = 0) :
    ∃ (b : Fin n) (t : Bool), pcol s = ucol b t ∧ b ≤ pidx s (pivot_pos hs) ∧
      ¬ (b = pidx s (pivot_pos hs) ∧ t = false) := by
  have hU := pivot_pos hs
  obtain ⟨b, hb, hz⟩ := pcol_unit s hU hk
  have hc : pcol s = ucol b (decide (pcol s b = -1)) := by
    funext r
    by_cases hr : r = b
    · subst hr; simp only [ucol, if_pos rfl]
      rcases hb with h | h <;> simp [h]
    · simp [ucol, hr, hz r hr]
  refine ⟨b, _, hc, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact (ucol_ne (b := b) (t := decide (pcol s b = -1)))
      (by rw [← hc]; exact pcol_zero_above s hU b h)
  · rintro ⟨rfl, ht⟩
    apply pcol_ne_unit s hU
    intro r
    rw [hc]; simp only [ucol]
    rw [ht]; simp

theorem pidx_congr {U V : O_ZHalf n} (hU : 0 < pivotJ U) (hV : 0 < pivotJ V)
    (h : pivotJ V = pivotJ U) : pidx V hV = pidx U hU := Fin.ext (by simp [pidx_val, h])

/-- The state `G s` when `G` moves `±e_b` to a column `±e_c` other than `e_j`. -/
theorem stateU {s : O_ZHalf n} (hs : s ≠ 1) {g : Gen n} (hb : extent g < pivotJ s) {c : Fin n}
    {t : Bool} (hcol : gact g (pcol s) = ucol c t)
    (hne : ¬ (c = pidx s (pivot_pos hs) ∧ t = false)) :
    ∃ hV : 0 < pivotJ (sem n g * s), pidx (sem n g * s) hV = pidx s (pivot_pos hs) ∧
      pcol (sem n g * s) = ucol c t := by
  have hU := pivot_pos hs
  have hl : BelowJ (pivotJ s) [g] := by
    intro g' hg'; rw [List.mem_singleton] at hg'; rw [hg']; exact hb
  obtain ⟨h1, h2⟩ := pcol_word s hU [g] hl (by
    rw [wact_single, hcol]
    intro hu
    have := hu c
    simp only [ucol, if_pos rfl] at this
    by_cases hcp : c = pidx s hU
    · rw [if_pos hcp] at this
      cases t
      · exact hne ⟨hcp, rfl⟩
      · norm_num at this
    · rw [if_neg hcp] at this; cases t <;> norm_num at this)
  rw [lift_single] at h1 h2
  have hV : 0 < pivotJ (sem n g * s) := by rw [h1]; exact hU
  exact ⟨hV, pidx_congr hU hV h1, by rw [h2, wact_single, hcol]⟩

/-- `G` makes the pivot column `e_j`: the pivot drops. -/
theorem stateU_drop {s : O_ZHalf n} (hs : s ≠ 1) {g : Gen n} (hb : extent g < pivotJ s)
    (hcol : gact g (pcol s) = ucol (pidx s (pivot_pos hs)) false) :
    level (sem n g * s) < level s := by
  have hU := pivot_pos hs
  have hl : BelowJ (pivotJ s) [g] := by
    intro g' hg'; rw [List.mem_singleton] at hg'; rw [hg']; exact hb
  have := pivot_word_lt s hU [g] hl (by
    rw [wact_single, hcol]; intro r; simp [ucol])
  rw [lift_single] at this
  exact level_lt_of hU (Or.inl this)

theorem gact_neg_ucol_ne {z b : Fin n} {t : Bool} (h : z ≠ b) :
    gact (Gen.neg z) (ucol b t) = ucol b t := by
  funext r; simp only [gact, ucol]
  by_cases hr : r = z
  · subst hr; simp [h]
  · simp [hr]

theorem gact_neg_ucol_eq (b : Fin n) (t : Bool) : gact (Gen.neg b) (ucol b t) = ucol b (!t) := by
  funext r; simp only [gact, ucol]
  by_cases hr : r = b
  · subst hr; cases t <;> simp
  · simp [hr]

theorem gact_x_ucol {x y : Fin n} (hxy : x < y) (b : Fin n) (t : Bool) :
    gact (Gen.x x y hxy) (ucol b t) = ucol (Equiv.swap x y b) t := by
  funext r; simp only [gact, ucol]
  congr 1
  exact propext ⟨fun h => by rw [← h, Equiv.swap_apply_self], fun h => by
    rw [h, Equiv.swap_apply_self]⟩

theorem negw_comm (t : Bool) (b z : Fin n) :
    Derivable (Table1 n) (FreeMonoid.ofList (negw t b) * FreeMonoid.of (Gen.neg z))
      (FreeMonoid.of (Gen.neg z) * FreeMonoid.ofList (negw t b)) := by
  cases t
  · simp only [negw, Bool.false_eq_true, ↓reduceIte, FreeMonoid.ofList_nil, one_mul, mul_one]
    exact Derivable.refl _
  · simp only [negw, ↓reduceIte, FreeMonoid.ofList_singleton]; exact neg_comm b z

/-- A word commuting with each letter of `negw`. -/
theorem negw_comm' (t : Bool) (b : Fin n) {w : Word (Gen n)}
    (h : Derivable (Table1 n) (FreeMonoid.of (Gen.neg b) * w) (w * FreeMonoid.of (Gen.neg b))) :
    Derivable (Table1 n) (FreeMonoid.ofList (negw t b) * w) (w * FreeMonoid.ofList (negw t b)) := by
  cases t
  · simp only [negw, Bool.false_eq_true, ↓reduceIte, FreeMonoid.ofList_nil, one_mul, mul_one]
    exact Derivable.refl _
  · simp only [negw, ↓reduceIte, FreeMonoid.ofList_singleton]; exact h

/-- `negw t y · X_[x,y] ≈ X_[x,y] · negw t x`. -/
theorem negw_swap {x y : Fin n} (hxy : x < y) (t : Bool) :
    Derivable (Table1 n) (FreeMonoid.ofList (negw t y) * FreeMonoid.of (Gen.x x y hxy))
      (FreeMonoid.of (Gen.x x y hxy) * FreeMonoid.ofList (negw t x)) := by
  cases t
  · simp only [negw, Bool.false_eq_true, ↓reduceIte, FreeMonoid.ofList_nil, one_mul, mul_one]
    exact Derivable.refl _
  · simp only [negw, ↓reduceIte, FreeMonoid.ofList_singleton]
    exact flipD (Derivable.of (Table1.r1a x y hxy)) (Derivable.of (Table1.r3c x y hxy))

/-- `negw t x · X_[x,y] ≈ X_[x,y] · negw t y`. -/
theorem negw_swap' {x y : Fin n} (hxy : x < y) (t : Bool) :
    Derivable (Table1 n) (FreeMonoid.ofList (negw t x) * FreeMonoid.of (Gen.x x y hxy))
      (FreeMonoid.of (Gen.x x y hxy) * FreeMonoid.ofList (negw t y)) := by
  cases t
  · simp only [negw, Bool.false_eq_true, ↓reduceIte, FreeMonoid.ofList_nil, one_mul, mul_one]
    exact Derivable.refl _
  · simp only [negw, ↓reduceIte, FreeMonoid.ofList_singleton]
    exact (Derivable.of (Table1.r3c x y hxy)).symm

/-- `A · w · B ≈ A · w' · B` from `w ≈ w'`, with the words written out. -/
theorem mid {A w w' B : Word (Gen n)} (h : Derivable (Table1 n) w w') :
    Derivable (Table1 n) (A * w * B) (A * w' * B) :=
  ((Derivable.refl A).mul h).mul (Derivable.refl B)

/-! ## Derivations between explicit words -/

/-- Replacing a segment of a word. -/
theorem stepL {l l' A B : List (Gen n)} (u v : List (Gen n))
    (h : Derivable (Table1 n) (FreeMonoid.ofList u) (FreeMonoid.ofList v))
    (h1 : l = A ++ u ++ B) (h2 : l' = A ++ v ++ B) :
    Derivable (Table1 n) (FreeMonoid.ofList l) (FreeMonoid.ofList l') := by
  subst h1; subst h2
  simp only [FreeMonoid.ofList_append]
  exact ((Derivable.refl _).mul h).mul (Derivable.refl _)

/-- A derivation between two words given as lists. -/
theorem DL_of {w w' : Word (Gen n)} (l l' : List (Gen n)) (e : w = FreeMonoid.ofList l)
    (e' : w' = FreeMonoid.ofList l')
    (h : Derivable (Table1 n) (FreeMonoid.ofList l) (FreeMonoid.ofList l')) :
    Derivable (Table1 n) w w' := by
  subst e; subst e'; exact h

theorem nd3 {a b c : Fin n} (h1 : a.val ≠ b.val) (h2 : a.val ≠ c.val) (h3 : b.val ≠ c.val) :
    [a, b, c].Nodup :=
  nodup_vals (by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    omega)

theorem nd4 {a b c d : Fin n} (h1 : a.val ≠ b.val) (h2 : a.val ≠ c.val) (h3 : a.val ≠ d.val)
    (h4 : b.val ≠ c.val) (h5 : b.val ≠ d.val) (h6 : c.val ≠ d.val) : [a, b, c, d].Nodup :=
  nodup_vals (by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    omega)

/-! ## `G = (−1)_[z]` -/

/-- Subcase 2.1. -/
theorem squareZ_N {s : O_ZHalf n} (hs : s ≠ 1) (hk : lde s = 0) {z : Fin n} (hz0 : z.val = 0)
    (hle : level (sem n (Gen.neg z) * s) ≤ level s) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.neg z) * s)) *
        FreeMonoid.of (Gen.neg z)) (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  have hb := extent_lt_of_le hs hle
  obtain ⟨b, t, hc, hbp, hne⟩ := col_zero hs hk
  set p := pidx s hU
  by_cases hzb : z = b
  · subst hzb
    rcases lt_or_eq_of_le hbp with hlt | heq
    · -- `b < j`: the sign flips
      obtain ⟨hV, hpV, hcV⟩ := stateU hs hb (by rw [hc, gact_neg_ucol_eq])
        (t := !t) (fun h => absurd h.1 (ne_of_lt hlt))
      refine square_short hs hle [] (by simp) ?_
      rw [syll_ucol_lt _ hV hpV hcV hlt, syll_ucol_lt s hU rfl hc hlt]
      cases t
      · exact DL_of [Gen.x z p hlt, Gen.neg z, Gen.neg z] [Gen.x z p hlt] rfl rfl
          (stepL (A := [Gen.x z p hlt]) (B := []) [Gen.neg z, Gen.neg z] []
            (Derivable.of (Table1.r1b z)) rfl rfl)
      · exact DL_of [Gen.x z p hlt, Gen.neg z] [Gen.x z p hlt, Gen.neg z] rfl rfl
          (Derivable.refl _)
    · -- `b = j`: the column becomes `e_j`
      have ht : t = true := by
        cases t
        · exact absurd ⟨heq, rfl⟩ hne
        · rfl
      subst ht
      have hlt := stateU_drop hs hb (by rw [hc, gact_neg_ucol_eq, heq]; rfl)
      refine square hs hle 0 [] (Or.inr hlt) ?_ (fun i hi0 hi => absurd hi (by simp))
      rw [syll_ucol_eq s hU (heq.symm) (by rw [hc, heq])]
      exact Derivable.refl _
  · -- `G` does not touch the column
    have hzp : z ≠ p := by
      intro e; apply hzb
      have : (b : ℕ) ≤ z := by rw [e]; exact hbp
      exact Fin.ext (by omega)
    have vzb : z.val ≠ b.val := fun e => hzb (Fin.ext e)
    have vzp : z.val ≠ p.val := fun e => hzp (Fin.ext e)
    obtain ⟨hV, hpV, hcV⟩ := stateU hs hb (by rw [hc, gact_neg_ucol_ne hzb]) hne
    refine square_short hs hle [Gen.neg z] (by simp) ?_
    rcases lt_or_eq_of_le hbp with hlt | heq
    · rw [syll_ucol_lt _ hV hpV hcV hlt, syll_ucol_lt s hU rfl hc hlt]
      have hbp' := Fin.lt_def.1 hlt
      have h2b : Derivable (Table1 n) (FreeMonoid.ofList [Gen.x b p hlt, Gen.neg z])
          (FreeMonoid.ofList [Gen.neg z, Gen.x b p hlt]) :=
        Derivable.of (Table1.r2b b p z hlt (nd3 (by omega) (by omega) (by omega)))
      cases t
      · exact DL_of _ _ rfl rfl (stepL (A := []) (B := []) _ _ h2b rfl rfl)
      · exact DL_of [Gen.x b p hlt, Gen.neg b, Gen.neg z] [Gen.neg z, Gen.x b p hlt, Gen.neg b]
          rfl rfl ((stepL (A := [Gen.x b p hlt]) (B := []) [Gen.neg b, Gen.neg z]
            [Gen.neg z, Gen.neg b] (neg_comm b z) rfl rfl).trans
            (stepL (A := []) (B := [Gen.neg b]) _ _ h2b rfl rfl))
    · have hcV' : pcol (sem n (Gen.neg z) * s) = ucol p t := by rw [hcV, heq]
      have hc' : pcol s = ucol p t := by rw [hc, heq]
      rw [syll_ucol_eq _ hV hpV hcV', syll_ucol_eq s hU rfl hc']
      exact neg_comm p z

/-! ## `G = X_[x,x+1]` -/

/-- Subcase 1.1. -/
theorem squareZ_X {s : O_ZHalf n} (hs : s ≠ 1) (hk : lde s = 0) {x y : Fin n} (hxy : x < y)
    (hy : y.val = x.val + 1) (hle : level (sem n (Gen.x x y hxy) * s) ≤ level s) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.x x y hxy) * s)) *
        FreeMonoid.of (Gen.x x y hxy)) (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  have hb := extent_lt_of_le hs hle
  obtain ⟨b, t, hc, hbp, hne⟩ := col_zero hs hk
  set p := pidx s hU
  have hyp : y.val ≤ p.val := by
    have : extent (Gen.x x y hxy) = y.val := rfl
    rw [pidx_val]; omega
  have vxy := Fin.lt_def.1 hxy
  have vbp := Fin.le_def.1 hbp
  have hX : Derivable (Table1 n) (FreeMonoid.ofList [Gen.x x y hxy, Gen.x x y hxy])
      (FreeMonoid.ofList []) := Derivable.of (Table1.r1a x y hxy)
  by_cases hbx : b = x
  · -- the column moves to `x + 1`
    subst hbx
    have hcol : gact (Gen.x b y hxy) (pcol s) = ucol y t := by
      rw [hc, gact_x_ucol, swap_x]
    rcases lt_or_eq_of_le hyp with hlt | heq
    · have hyp' : y < p := Fin.lt_def.2 hlt
      have hbp' : b < p := hxy.trans hyp'
      obtain ⟨hV, hpV, hcV⟩ := stateU hs hb hcol (fun h => absurd h.1 (ne_of_lt hyp'))
      refine square_short hs hle [Gen.x b y hxy] (by simp) ?_
      rw [syll_ucol_lt _ hV hpV hcV hyp', syll_ucol_lt s hU rfl hc hbp']
      have h3a : Derivable (Table1 n) (FreeMonoid.ofList [Gen.x y p hyp', Gen.x b y hxy])
          (FreeMonoid.ofList [Gen.x b y hxy, Gen.x b p hbp']) :=
        (Derivable.of (Table1.r3a b y p hxy hyp')).symm
      cases t
      · exact DL_of _ _ rfl rfl (stepL (A := []) (B := []) _ _ h3a rfl rfl)
      · exact DL_of [Gen.x y p hyp', Gen.neg y, Gen.x b y hxy]
          [Gen.x b y hxy, Gen.x b p hbp', Gen.neg b] rfl rfl
          ((stepL (A := [Gen.x y p hyp']) (B := []) [Gen.neg y, Gen.x b y hxy]
            [Gen.x b y hxy, Gen.neg b]
            (flipD hX (Derivable.of (Table1.r3c b y hxy))) rfl rfl).trans
            (stepL (A := []) (B := [Gen.neg b]) _ _ h3a rfl rfl))
    · have hyP : y = p := Fin.ext heq
      cases t
      · -- the column becomes `e_j`
        have hlt := stateU_drop hs hb (by rw [hcol, hyP])
        refine square hs hle 0 [] (Or.inr hlt) ?_ (fun i hi0 hi => absurd hi (by simp))
        rw [syll_ucol_lt s hU hyP.symm hc hxy]
        exact Derivable.refl _
      · obtain ⟨hV, hpV, hcV⟩ := stateU hs hb hcol (fun h => Bool.noConfusion h.2)
        refine square_short hs hle [] (by simp) ?_
        rw [syll_ucol_eq _ hV (hpV.trans hyP.symm) hcV, syll_ucol_lt s hU hyP.symm hc hxy]
        exact DL_of [Gen.neg y, Gen.x b y hxy] [Gen.x b y hxy, Gen.neg b] rfl rfl
          (flipD hX (Derivable.of (Table1.r3c b y hxy)))
  by_cases hby : b = y
  · -- the column moves to `x`
    subst hby
    have hcol : gact (Gen.x x b hxy) (pcol s) = ucol x t := by
      rw [hc, gact_x_ucol, swap_y]
    have hxp : x < p := Fin.lt_def.2 (by omega)
    obtain ⟨hV, hpV, hcV⟩ := stateU hs hb hcol (fun h => absurd h.1 (ne_of_lt hxp))
    rcases lt_or_eq_of_le hbp with hlt | heq
    · refine square_short hs hle [Gen.x x b hxy] (by simp) ?_
      rw [syll_ucol_lt _ hV hpV hcV hxp, syll_ucol_lt s hU rfl hc hlt]
      have h3a : Derivable (Table1 n) (FreeMonoid.ofList [Gen.x x p hxp, Gen.x x b hxy])
          (FreeMonoid.ofList [Gen.x x b hxy, Gen.x b p hlt]) :=
        flipD hX (Derivable.of (Table1.r3a x b p hxy hlt))
      cases t
      · exact DL_of _ _ rfl rfl (stepL (A := []) (B := []) _ _ h3a rfl rfl)
      · exact DL_of [Gen.x x p hxp, Gen.neg x, Gen.x x b hxy]
          [Gen.x x b hxy, Gen.x b p hlt, Gen.neg b] rfl rfl
          ((stepL (A := [Gen.x x p hxp]) (B := []) [Gen.neg x, Gen.x x b hxy]
            [Gen.x x b hxy, Gen.neg b] (Derivable.of (Table1.r3c x b hxy)).symm rfl rfl).trans
            (stepL (A := []) (B := [Gen.neg b]) _ _ h3a rfl rfl))
    · have ht : t = true := by
        cases t
        · exact absurd ⟨heq, rfl⟩ hne
        · rfl
      subst ht
      refine square_short hs hle [] (by simp) ?_
      rw [syll_ucol_lt _ hV (hpV.trans heq.symm) hcV hxy, syll_ucol_eq s hU heq.symm hc]
      exact DL_of [Gen.x x b hxy, Gen.neg x, Gen.x x b hxy] [Gen.neg b] rfl rfl
        ((stepL (A := [Gen.x x b hxy]) (B := []) [Gen.neg x, Gen.x x b hxy]
          [Gen.x x b hxy, Gen.neg b] (Derivable.of (Table1.r3c x b hxy)).symm rfl rfl).trans
          (stepL (A := []) (B := [Gen.neg b]) [Gen.x x b hxy, Gen.x x b hxy] [] hX rfl rfl))
  · -- the column does not move
    have hcol : gact (Gen.x x y hxy) (pcol s) = ucol b t := by
      rw [hc, gact_x_ucol, swap_o hbx hby]
    obtain ⟨hV, hpV, hcV⟩ := stateU hs hb hcol hne
    have vbx : b.val ≠ x.val := fun e => hbx (Fin.ext e)
    have vby : b.val ≠ y.val := fun e => hby (Fin.ext e)
    rcases lt_or_eq_of_le hbp with hlt | heq
    · have vbp' := Fin.lt_def.1 hlt
      by_cases hyP : y = p
      · -- `b < x`, and the square is closed by `X_[b,x]`
        have hbx' : b < x := Fin.lt_def.2 (by rw [hyP] at hy; omega)
        have hby' : b < y := hbx'.trans hxy
        refine square_short hs hle [Gen.x b x hbx'] (by simp) ?_
        rw [syll_ucol_lt _ hV (hpV.trans hyP.symm) hcV hby', syll_ucol_lt s hU hyP.symm hc hby']
        have h3 : Derivable (Table1 n) (FreeMonoid.ofList [Gen.x b y hby', Gen.x x y hxy])
            (FreeMonoid.ofList [Gen.x b x hbx', Gen.x b y hby']) :=
          (Derivable.of (Table1.r3b b x y hbx' hxy)).symm.trans
            (Derivable.of (Table1.r3a b x y hbx' hxy)).symm
        cases t
        · exact DL_of _ _ rfl rfl (stepL (A := []) (B := []) _ _ h3 rfl rfl)
        · exact DL_of [Gen.x b y hby', Gen.neg b, Gen.x x y hxy]
            [Gen.x b x hbx', Gen.x b y hby', Gen.neg b] rfl rfl
            ((stepL (A := [Gen.x b y hby']) (B := []) [Gen.neg b, Gen.x x y hxy]
              [Gen.x x y hxy, Gen.neg b]
              (Derivable.of (Table1.r2b x y b hxy (nd3 (by omega) (by omega) (by omega)))).symm
              rfl rfl).trans
              (stepL (A := []) (B := [Gen.neg b]) _ _ h3 rfl rfl))
      · have vyp : y.val ≠ p.val := fun e => hyP (Fin.ext e)
        refine square_short hs hle [Gen.x x y hxy] (by simp) ?_
        rw [syll_ucol_lt _ hV hpV hcV hlt, syll_ucol_lt s hU rfl hc hlt]
        have h2a : Derivable (Table1 n) (FreeMonoid.ofList [Gen.x b p hlt, Gen.x x y hxy])
            (FreeMonoid.ofList [Gen.x x y hxy, Gen.x b p hlt]) :=
          (Derivable.of (Table1.r2a x y b p hxy hlt
            (nd4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))).symm
        cases t
        · exact DL_of _ _ rfl rfl (stepL (A := []) (B := []) _ _ h2a rfl rfl)
        · exact DL_of [Gen.x b p hlt, Gen.neg b, Gen.x x y hxy]
            [Gen.x x y hxy, Gen.x b p hlt, Gen.neg b] rfl rfl
            ((stepL (A := [Gen.x b p hlt]) (B := []) [Gen.neg b, Gen.x x y hxy]
              [Gen.x x y hxy, Gen.neg b]
              (Derivable.of (Table1.r2b x y b hxy (nd3 (by omega) (by omega) (by omega)))).symm
              rfl rfl).trans
              (stepL (A := []) (B := [Gen.neg b]) _ _ h2a rfl rfl))
    · refine square_short hs hle [Gen.x x y hxy] (by simp) ?_
      rw [syll_ucol_eq _ hV (hpV.trans heq.symm) hcV, syll_ucol_eq s hU heq.symm hc]
      exact DL_of [Gen.neg b, Gen.x x y hxy] [Gen.x x y hxy, Gen.neg b] rfl rfl
        (Derivable.of (Table1.r2b x y b hxy (nd3 (by omega) (by omega) (by omega)))).symm

end QCert.LiRossSelinger
