/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (342) from five wires on

The multi-controlled `H` `A` with its box on wire `0` and its `H` on wire `1`
(control `2` of colour `c₁`, the wires `3, …` coloured by `x`) commutes with
the multi-controlled `H` `B` with its box on wire `0` and its `H` on wire `2`
(control `1` of colour `c₂`, the wires `3, …` coloured by `y`), when
`x ≠ y`.

As for (339), (344) (`Low339`, `Low344`): the colourings may be assumed to
differ on wire `3`, black for `x` (`sep_reduce`).  `A` is written as in
(344), `(P S₂) · Abox · (S₂ P)` (`L344.expA`).  `B` is `W · Bbox · W'` with
`W = S₁ (P ⊗ P) S₁ S₂`, `Bbox` the box of (339) (`c₂` on wire `1`, white on
wire `2`, black on wire `3`): `B` is `P ⊗ P` on its box wire `0` and its `H`
wire `2` around the box with a black control on wire `2` (Definition 2.4,
relabeled by the swap of the wires `1, 2`), and that box is `Bbox` under the
swap of the wires `2, 3`.  Both remainders are idle on wire `2`, the `H` wire
of `B`.  The pieces commute pairwise:

* two rotations: a semantic step without wire `4` (`SepSem`);
* a rotation of `A` and the remainder of `B`: the remainder conjugated by
  `W` is, by (276), the box idle on wire `2`, and this is (322)/(323)
  (`E337.commR_ppB`) between `P ⊗ P`;
* the remainders: `BoxPPBridge.commBBpp`;
* the remainder of `A` and a rotation of `B`: conjugated by `W'`, the
  remainder of `A` is `P ⊗ P` around the box of `E336x`, by the Klein
  four-group of the `P ⊗ P` on the wires `0, 1, 2` and (276), and this is
  (322)/(323) (`E337.commB_ppRw`).

Every step holds from five wires on (`comm342_ge5`); `eq342_5` is the case
`N = 5`.

Memory (2026-10-29): about 30 s, peak 0.32 GB anonymous (3.2 GB resident
with the mapped imports).
-/
import QCert.RealCliffordCH.Sec8.D.N13.Low344

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.L342

open Circuit Eng SE Net N8 Sep L339 L344

/-- The controls of the second multi-controlled `H` of (342). -/
abbrev cB2 (N : ℕ) (y : ℕ → Bool) (c₂ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 1 c₂) (colOn 3 N y)

/-- The conjugating word of `B`: `S₁ (P ⊗ P) S₁ S₂`, and its reverse. -/
abbrev W (m : ℕ) : Circ (m + 5) :=
  swAt (m + 5) 1 * (pp : Circ (m + 5)) * swAt (m + 5) 1 * swAt (m + 5) 2
abbrev W' (m : ℕ) : Circ (m + 5) :=
  swAt (m + 5) 2 * swAt (m + 5) 1 * (pp : Circ (m + 5)) * swAt (m + 5) 1

/-! ## Words for the semantic steps -/

/-- The words of `W'` and `W` in drawn order. -/
def bL : List Lt := [Lt.s (L.S 1)] ++ N13.ppL ++ [Lt.s (L.S 1), Lt.s (L.S 2)]
def bR : List Lt := [Lt.s (L.S 2), Lt.s (L.S 1)] ++ N13.ppL ++ [Lt.s (L.S 1)]

theorem rt_bL : rtW bL 3 = some 2 := by decide
theorem rt_bR : rtW bR 2 = some 3 := by decide

theorem b_drop : ∀ x ∈ bL ++ bR,
    x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x ∧ x.ok 4 = true := by decide

theorem wcbR (K k : ℕ) : wc K (k + 2) bR =
    swAt (k + 2) 1 * (pp : Circ (k + 2)) * swAt (k + 2) 1 * swAt (k + 2) 2 := by
  simp only [bR, wc_append, wc_two, drawn_two, wc_one', circS, wc_ppL', mul_assoc]

theorem wcbL (K k : ℕ) : wc K (k + 2) bL =
    swAt (k + 2) 2 * swAt (k + 2) 1 * (pp : Circ (k + 2)) * swAt (k + 2) 1 := by
  simp only [bL, wc_append, wc_two, drawn_two, wc_one', circS, wc_ppL', mul_assoc]

theorem bRL (n : ℕ) (ihn : IH (n + 4)) :
    Derivable (theory (n + 4)) (wc 4 (n + 4) bR * wc 4 (n + 4) bL) 1 := by
  rw [wcbR 4 (n + 2), wcbL 4 (n + 2)]
  have e : swAt (n + 4) 1 * (pp : Circ (n + 4)) * swAt (n + 4) 1 * swAt (n + 4) 2 *
      (swAt (n + 4) 2 * swAt (n + 4) 1 * (pp : Circ (n + 4)) * swAt (n + 4) 1) =
      swAt (n + 4) 1 * ((pp : Circ (n + 4)) * (swAt (n + 4) 1 * (swAt (n + 4) 2 *
        swAt (n + 4) 2) * swAt (n + 4) 1) * pp) * swAt (n + 4) 1 := by simp only [mul_assoc]
  rw [e]
  exact L339.palin (swsw (n + 4) 1 (by omega)) (L339.palin (pp_inv (n + 1) ihn)
    (L339.palin (swsw (n + 4) 1 (by omega)) (swsw (n + 4) 2 (by omega))))

section Frame

variable (m : ℕ) (ih : IH (m + 5))
include ih

theorem WW' : Derivable (theory (m + 5)) (W m * W' m) 1 := by
  have e : W m * W' m = swAt (m + 5) 1 * ((pp : Circ (m + 5)) * (swAt (m + 5) 1 *
      (swAt (m + 5) 2 * swAt (m + 5) 2) * swAt (m + 5) 1) * pp) * swAt (m + 5) 1 := by
    simp only [W, W', mul_assoc]
  rw [e]
  exact L339.palin (hs m ih 1 (by omega)) (L339.palin (hpp m ih)
    (L339.palin (hs m ih 1 (by omega)) (hs m ih 2 (by omega))))

theorem W'W : Derivable (theory (m + 5)) (W' m * W m) 1 := by
  have e : W' m * W m = swAt (m + 5) 2 * (swAt (m + 5) 1 * ((pp : Circ (m + 5)) *
      (swAt (m + 5) 1 * swAt (m + 5) 1) * pp) * swAt (m + 5) 1) * swAt (m + 5) 2 := by
    simp only [W, W', mul_assoc]
  rw [e]
  exact L339.palin (hs m ih 2 (by omega)) (L339.palin (hs m ih 1 (by omega))
    (L339.palin (hpp m ih) (hs m ih 1 (by omega))))

/-! ### `B` -/

/-- `B` as `W · Bbox · W'`. -/
theorem hgW (y : ℕ → Bool) (c₂ : Bool) (hy : y 3 = false) :
    Derivable (theory (m + 5)) (mc (m + 5) .hg [0, 2] (cB2 (m + 5) y c₂))
      (W m * mc (m + 5) .box [0] (colOn 1 (m + 5) (yB c₂ y)) * W' m) := by
  have t2 := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0] (colOn 1 (m + 5) (yB c₂ y))
    (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 2 true) (colOn 3 (m + 5) y))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [colOn, ctlOr, ctlAt, yB, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  have s1 := swBH ih 1 (by omega) .hg (Or.inr rfl) [0, 1] [0, 2]
    (colOn 2 (m + 5) (yP c₂ y)) (cB2 (m + 5) y c₂) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have hp : Derivable (theory (m + 5)) (mc (m + 5) .hg [0, 1] (colOn 2 (m + 5) (yP c₂ y)))
      ((pp : Circ (m + 5)) * bA (m + 5) (yP c₂ y) true * pp) := hg0_box4 (m + 1) (yP c₂ y)
  have t1 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 2 true) (colOn 3 (m + 5) y)))
    (ctlOr (ctlAt 1 true) (colOn 2 (m + 5) (yP c₂ y))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have k1 := hp.trans (dctx _ _ (t1.symm.trans (dctx _ _ t2.symm)))
  have k2 := s1.symm.trans (dctx _ _ k1)
  have e : swAt (m + 5) 1 * ((pp : Circ (m + 5)) * (swAt (m + 5) 1 *
      (swAt (m + 5) 2 * mc (m + 5) .box [0] (colOn 1 (m + 5) (yB c₂ y)) * swAt (m + 5) 2) *
      swAt (m + 5) 1) * pp) * swAt (m + 5) 1 =
      W m * mc (m + 5) .box [0] (colOn 1 (m + 5) (yB c₂ y)) * W' m := by
    simp only [W, W', mul_assoc]
  rw [e] at k2
  exact k2

/-- `B` as the conjugated pieces of the expansion. -/
theorem expB (y : ℕ → Bool) (c₂ : Bool) (hy : y 3 = false) :
    Derivable (theory (m + 5)) (mc (m + 5) .hg [0, 2] (cB2 (m + 5) y c₂))
      (drawn (((pcs4 c₂ false true).map (cX 4 (m + 5) (yB c₂ y))).map
        (fun a => W m * a * W' m))) := by
  have ex := expX (m + 5) (by omega) ih (yB c₂ y)
  rw [yB1, yB2, yB3] at ex
  exact (hgW m ih y c₂ hy).trans ((conj_eq ex).trans (conj_drawn (W'W m ih) (WW' m ih) _))

/-! ### The remainders -/

/-- The remainder of `B` conjugated by `W`: (276). -/
theorem remB (z : ℕ → Bool) (c₂ : Bool) :
    Derivable (theory (m + 5)) (W m * boxN (m + 5) z c₂ false * W' m)
      (swAt (m + 5) 2 * boxN (m + 5) z c₂ false * swAt (m + 5) 2) := by
  have a1 := g1 m ih z c₂ false
  have e : W m * boxN (m + 5) z c₂ false * W' m =
      P02 m * (swAt (m + 5) 2 * boxN (m + 5) z c₂ false * swAt (m + 5) 2) * P02 m := by
    simp only [W, W', P02, mul_assoc]
  rw [e]
  exact (conj_eq a1).trans ((p1g m ih z c₂ false).trans a1.symm)

/-- The remainder of `A` conjugated by `W'`: `P ⊗ P` around the box of
`E336x`. -/
theorem kR3 (z : ℕ → Bool) :
    Derivable (theory (m + 5))
      (W' m * (((pp : Circ (m + 5)) * swAt (m + 5) 2) * boxN (m + 5) z true true *
        (swAt (m + 5) 2 * pp)) * W m)
      ((pp : Circ (m + 5)) * boxN (m + 5) z true true * pp) := by
  have hs2 := hs m ih 2 (by omega)
  have a1 := g1 m ih z true true
  have q := q2 m ih
  have e0 : W' m * (((pp : Circ (m + 5)) * swAt (m + 5) 2) * boxN (m + 5) z true true *
        (swAt (m + 5) 2 * pp)) * W m =
      swAt (m + 5) 2 * ((P02 m * pp) * (swAt (m + 5) 2 * boxN (m + 5) z true true *
        swAt (m + 5) 2) * (pp * P02 m)) * swAt (m + 5) 2 := by
    simp only [W, W', P02, mul_assoc]
  rw [e0]
  -- the Klein four-group and (276)
  have k1 : Derivable (theory (m + 5))
      ((P02 m * pp) * (swAt (m + 5) 2 * boxN (m + 5) z true true * swAt (m + 5) 2) *
        (pp * P02 m))
      ((pp : Circ (m + 5)) * bxR (m + 5) 0 1 3 true true z * pp) := by
    refine (dmul (dmul ((klein3 m ih).trans (klein4 m ih).symm) a1)
      ((klein4 m ih).trans (klein3 m ih).symm)).trans ?_
    have e : (pp : Circ (m + 5)) * P02 m * bxR (m + 5) 0 1 3 true true z * (P02 m * pp) =
        pp * (P02 m * bxR (m + 5) 0 1 3 true true z * P02 m) * pp := by simp only [mul_assoc]
    rw [e]
    exact conj_eq (p1g m ih z true true)
  -- `S₂` through `P ⊗ P`
  have k2 : Derivable (theory (m + 5))
      (swAt (m + 5) 2 * ((pp : Circ (m + 5)) * bxR (m + 5) 0 1 3 true true z * pp) * swAt (m + 5) 2)
      ((pp : Circ (m + 5)) * boxN (m + 5) z true true * pp) := by
    have e : swAt (m + 5) 2 * ((pp : Circ (m + 5)) * bxR (m + 5) 0 1 3 true true z * pp) *
        swAt (m + 5) 2 = (swAt (m + 5) 2 * pp) * bxR (m + 5) 0 1 3 true true z *
        (pp * swAt (m + 5) 2) := by simp only [mul_assoc]
    rw [e]
    refine (dmul (dmul q (Derivable.refl _)) q.symm).trans ?_
    have e2 : (pp : Circ (m + 5)) * swAt (m + 5) 2 * bxR (m + 5) 0 1 3 true true z *
        (swAt (m + 5) 2 * pp) =
        pp * (swAt (m + 5) 2 * bxR (m + 5) 0 1 3 true true z * swAt (m + 5) 2) * pp := by
      simp only [mul_assoc]
    rw [e2]
    exact conj_eq (conj_back hs2 a1)
  exact (conj_eq k1).trans k2

/-! ### The pairs -/

set_option maxRecDepth 20000 in
/-- Two rotations: `(P S₂) r (S₂ P)` and `W r' W'` live on the wires `0–3`
and are trivial on complementary blocks of wire `3`. -/
theorem commRR {c₁ c₃ : Bool} {r r' : Lt} (hr : r ∈ rots true true c₁)
    (hr' : r' ∈ rots c₃ false true) :
    Comm (m + 5) (((pp : Circ (m + 5)) * swAt (m + 5) 2) * r.circ 4 (m + 5) * (swAt (m + 5) 2 * pp))
      (W m * r'.circ 4 (m + 5) * W' m) := by
  have ih4 : IH (m + 4) := ih.mono (by omega)
  have hA := rot_drop _ _ _ r hr
  have hB := rot_drop _ _ _ r' hr'
  have hu := b_drop
  have ha := a_drop
  have tA : Triv 3 0 (opsQ.eval (m + 4) (wc 4 (m + 4) (aL ++ [r] ++ aR))) := by
    rw [wc_conj]
    have hX := triv_rot (m + 4) (by omega) hr
    simp only [if_true] at hX
    exact triv_conj (K := 4) (by omega) (fun x hx => (ha x (by simp [hx])).2.2.2)
      (fun x hx => (ha x (by simp [hx])).2.2.2) (by omega) (by omega) rt_aL rt_aR
      (eval_inv (aRL m ih4)) hX
  have tB : Triv 3 1 (opsQ.eval (m + 4) (wc 4 (m + 4) (bL ++ [r'] ++ bR))) := by
    rw [wc_conj]
    have hX := triv_rot (m + 4) (by omega) hr'
    simp only [Bool.false_eq_true, if_false] at hX
    exact triv_conj (K := 4) (by omega) (fun x hx => (hu x (by simp [hx])).2.2.2)
      (fun x hx => (hu x (by simp [hx])).2.2.2) (by omega) (by omega) rt_bL rt_bR
      (eval_inv (bRL m ih4)) hX
  have hsem := sep_sem (K := 4) (M := m + 4) (by decide : (0 : Fin 2) ≠ 1) tA tB
  have mem : ∀ x ∈ (aL ++ [r] ++ aR) ++ (bL ++ [r'] ++ bR),
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((hx | rfl) | hx) | ((hx | rfl) | hx)
    · exact (ha x (by simp [hx])).imp_right (fun h => ⟨h.1, h.2.1⟩)
    · exact ⟨hA.1, hA.2.1, hA.2.2.1⟩
    · exact (ha x (by simp [hx])).imp_right (fun h => ⟨h.1, h.2.1⟩)
    · exact (hu x (by simp [hx])).imp_right (fun h => ⟨h.1, h.2.1⟩)
    · exact ⟨hB.1, hB.2.1, hB.2.2.1⟩
    · exact (hu x (by simp [hx])).imp_right (fun h => ⟨h.1, h.2.1⟩)
  have mem' : ∀ x ∈ (bL ++ [r'] ++ bR) ++ (aL ++ [r] ++ aR),
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := fun x hx =>
    mem x (by simp only [List.mem_append] at hx ⊢; tauto)
  have e1 : ((aL ++ [r] ++ aR) ++ (bL ++ [r'] ++ bR)).map (Lt.drop 4) =
      (aL ++ [r] ++ aR) ++ (bL ++ [r'] ++ bR) := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem x hx).2.2), List.map_id]
  have e2 : ((bL ++ [r'] ++ bR) ++ (aL ++ [r] ++ aR)).map (Lt.drop 4) =
      (bL ++ [r'] ++ bR) ++ (aL ++ [r] ++ aR) := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem' x hx).2.2), List.map_id]
  rw [← e1, ← e2] at hsem
  have hw : Derivable (theory (m + 5))
      (wc 5 (m + 5) ((aL ++ [r] ++ aR) ++ (bL ++ [r'] ++ bR)))
      (wc 5 (m + 5) ((bL ++ [r'] ++ bR) ++ (aL ++ [r] ++ aR))) :=
    SE.Frame.window (frame 4) m ih (q := 4) le_rfl
      (fun x hx => ⟨(mem x hx).1, (mem x hx).2.1⟩) (fun x hx => ⟨(mem' x hx).1, (mem' x hx).2.1⟩)
      hsem
  have eA : wc 5 (m + 5) (aL ++ [r] ++ aR) =
      ((pp : Circ (m + 5)) * swAt (m + 5) 2) * r.circ 4 (m + 5) * (swAt (m + 5) 2 * pp) := by
    rw [wc_conj, wcaR 5 (m + 3), wcaL 5 (m + 3), rots_rebase hr]
  have eB : wc 5 (m + 5) (bL ++ [r'] ++ bR) = W m * r'.circ 4 (m + 5) * W' m := by
    rw [wc_conj, wcbR 5 (m + 3), wcbL 5 (m + 3), rots_rebase hr']
  unfold Comm
  rw [drawn_two, drawn_two]
  rw [wc_append 5 (m + 5) (aL ++ [r] ++ aR) (bL ++ [r'] ++ bR),
    wc_append 5 (m + 5) (bL ++ [r'] ++ bR) (aL ++ [r] ++ aR), eA, eB] at hw
  exact hw

/-- A rotation of `A` and the remainder of `B`: (322)/(323) between `P ⊗ P`. -/
theorem commRQ (z : ℕ → Bool) (c₁ c₂ : Bool) {r : Lt} (hr : r ∈ rots true true c₁) :
    Comm (m + 5) (((pp : Circ (m + 5)) * swAt (m + 5) 2) * r.circ 4 (m + 5) * (swAt (m + 5) 2 * pp))
      (W m * boxN (m + 5) z c₂ false * W' m) := by
  obtain ⟨one, a, β, rfl⟩ := rots_Rr hr
  have h1 := commR_ppB m ih z one a c₁ β c₂
  have h3 := Comm.conj h1 (vInv2 m ih) (u := (pp : Circ (m + 5)) * swAt (m + 5) 2)
    (v := swAt (m + 5) 2 * pp)
  exact Comm.congr (Derivable.refl _) ((conjV m ih _).trans (remB m ih z c₂).symm) h3

/-- The two remainders: `BoxPPBridge.commBBpp`. -/
theorem commBQ (z w : ℕ → Bool) (c₂ : Bool) :
    Comm (m + 5)
      (((pp : Circ (m + 5)) * swAt (m + 5) 2) * boxN (m + 5) z true true * (swAt (m + 5) 2 * pp))
      (W m * boxN (m + 5) w c₂ false * W' m) := by
  have h := commBBpp m ih false false true c₂ z w
  have e1 : mc (m + 5) .box [boxTarget false] (boxCtl4 (m + 5) false true true z) =
      boxN (m + 5) z true true := mc_congr _ _ _ (by unfold boxCtl4 boxCtl; ctl_eq)
  have e2 : mc (m + 5) .box [boxTarget false] (boxCtl4 (m + 5) false c₂ false w) =
      boxN (m + 5) w c₂ false := mc_congr _ _ _ (by unfold boxCtl4 boxCtl; ctl_eq)
  rw [e1, e2] at h
  have h3 := Comm.conj h (vInv2 m ih) (u := (pp : Circ (m + 5)) * swAt (m + 5) 2)
    (v := swAt (m + 5) 2 * pp)
  exact Comm.congr (Derivable.refl _) ((conjV m ih _).trans (remB m ih w c₂).symm) h3

/-- The remainder of `A` and a rotation of `B`: (322)/(323) between `P ⊗ P`. -/
theorem commBR (z : ℕ → Bool) (c₂ : Bool) {r' : Lt} (hr' : r' ∈ rots c₂ false true) :
    Comm (m + 5)
      (((pp : Circ (m + 5)) * swAt (m + 5) 2) * boxN (m + 5) z true true * (swAt (m + 5) 2 * pp))
      (W m * r'.circ 4 (m + 5) * W' m) := by
  obtain ⟨one, a, β, rfl⟩ := rots_Rw hr'
  have h1 := commB_ppRw m ih z true one a true β
  have h2 := Comm.congr (Derivable.refl _) (pp_pp_conj ih _)
    (Comm.conj h1 (hpp m ih) (u := pp) (v := pp))
  exact conj_comm m ih (WW' m ih) (W'W m ih) (Comm.congr (kR3 m ih z).symm (Derivable.refl _) h2)

theorem pairs (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    ∀ a ∈ ((pcs4 true true c₁).map (cX 4 (m + 5) (xE c₁ true x))).map
        (fun a => ((pp : Circ (m + 5)) * swAt (m + 5) 2) * a * (swAt (m + 5) 2 * pp)),
      ∀ b ∈ ((pcs4 c₂ false true).map (cX 4 (m + 5) (yB c₂ y))).map
        (fun a => W m * a * W' m), Comm (m + 5) a b := by
  intro a ha b hb
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha0
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb0
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']; exact commRR m ih hr hr'
  · rw [rots_cX hr, P3'_cX]; exact commRQ m ih (yB c₂ y) c₁ c₂ hr
  · rw [P3'_cX, rots_cX hr']; exact commBR m ih (xE c₁ true x) c₂ hr'
  · rw [P3'_cX, P3'_cX]; exact commBQ m ih (xE c₁ true x) (yB c₂ y) c₂

/-- (342) when the colourings are black, resp. white, on wire `3`. -/
theorem core342 (x y : ℕ → Bool) (c₁ c₂ : Bool) (hx : x 3 = true) (hy : y 3 = false) :
    Comm (m + 5) (mc (m + 5) .hg [0, 1] (cA4 (m + 5) x c₁))
      (mc (m + 5) .hg [0, 2] (cB2 (m + 5) y c₂)) :=
  Comm.congr (L344.expA m ih x c₁ hx).symm (expB m ih y c₂ hy).symm
    (comm_drawn _ _ (pairs m ih x y c₁ c₂))

end Frame

/-! ## Back to the interface -/

/-- (342) from five wires on. -/
theorem comm342_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [0, 2] (ctlOr (ctlAt 1 c₂) (colOn 3 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 5) (mc (m + 5) .hg [0, 1] (cA4 (m + 5) x c₁))
    (mc (m + 5) .hg [0, 2] (cB2 (m + 5) y c₂))) ?_ ?_
    (fun x y hx hy => core342 m ih x y c₁ c₂ hx hy) x y hxy
  · intro x y j hj hjN h
    have rA := swBH ih j hjN .hg (Or.inr rfl) [0, 1] [0, 1] (cA4 (m + 5) (x ∘ Net.tau j) c₁)
      (cA4 (m + 5) x c₁) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau_of_lt (show 0 < j by omega),
        Net.tau_of_lt (show 1 < j by omega)])
      (fun i hi => by
        simp only [cA4, ctlOr, ctlAt_tau (show 2 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN x hi])
    have rB := swBH ih j hjN .hg (Or.inr rfl) [0, 2] [0, 2] (cB2 (m + 5) (y ∘ Net.tau j) c₂)
      (cB2 (m + 5) y c₂) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau_of_lt (show 0 < j by omega),
        Net.tau_of_lt (show 2 < j by omega)])
      (fun i hi => by
        simp only [cB2, ctlOr, ctlAt_tau (show 1 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN y hi])
    exact Comm.congr rA rB (Comm.conj h (swsw _ j hjN))
  · intro x y h
    have hx := xAt_inv (m + 5) 3 (by omega)
    refine comm_flip h hx ?_ ?_
    · have e := eq81 (m + 5) .hg [0, 1] (cA4 (m + 5) (flipAt 3 x) c₁) 3 (flipAt 3 x 3)
        (by omega) (by decide) (by simp [cA4, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 5) 3, mc (m + 5) .hg [0, 1] (cA4 (m + 5) (flipAt 3 x) c₁),
          xAt (m + 5) 3] = xAt (m + 5) 3 * mc (m + 5) .hg [0, 1] (cA4 (m + 5) (flipAt 3 x) c₁) *
          xAt (m + 5) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 5) (by omega) x i
      simp only [cA4, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all
    · have e := eq81 (m + 5) .hg [0, 2] (cB2 (m + 5) (flipAt 3 y) c₂) 3 (flipAt 3 y 3)
        (by omega) (by decide) (by simp [cB2, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 5) 3, mc (m + 5) .hg [0, 2] (cB2 (m + 5) (flipAt 3 y) c₂),
          xAt (m + 5) 3] = xAt (m + 5) 3 * mc (m + 5) .hg [0, 2] (cB2 (m + 5) (flipAt 3 y) c₂) *
          xAt (m + 5) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 5) (by omega) y i
      simp only [cB2, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all

/-- (342) on five wires, in the form of the interface `D.eq342`. -/
theorem eq342_5 (ih : IH 5) (x y : ℕ → Bool) (hxy : DiffOn 3 5 x y) (c₁ c₂ : Bool) :
    Comm 5 (mc 5 .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 5 x)))
      (mc 5 .hg [0, 2] (ctlOr (ctlAt 1 c₂) (colOn 3 5 y))) :=
  comm342_ge5 5 le_rfl ih x y hxy c₁ c₂

end QCert.RealCliffordCH.Sec8.D.N13.L342
