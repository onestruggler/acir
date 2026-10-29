/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (344) from five wires on

The multi-controlled `H` `A` with its box on wire `0` and its `H` on wire `1`
(control `2` of colour `c₁`, the wires `3, …` coloured by `x`) commutes with
the multi-controlled `H` `B` with its box on wire `1` and its `H` on wire `2`
(control `0` of colour `c₂`, the wires `3, …` coloured by `y`), when
`x ≠ y`.

As for (339) (`Low339`): the colourings may be assumed to differ on wire
`3`, black for `x` (`sep_reduce`).  `B` is `U · Bbox · U'` exactly as in
(339).  `A` is `P ⊗ P` around the box with a black control on its `H` wire
(Definition 2.4, `hg0_box4`), that is `(P S₂) · Abox · (S₂ P)` with `Abox`
the box of (339) with `c₂` black.  The pieces commute pairwise:

* two rotations: a semantic step without wire `4` (`SepSem`);
* a rotation of `A` and the remainder of `B`: (322)/(323) (`E337.commR_ppB`)
  under the swap of the wires `0, 1`;
* the remainders: `BoxPPBridge.commBBpp`;
* the remainder of `A` and a rotation of `B`: conjugated by `U'`, the
  remainder of `A` is `S₀ X S₀` by the Klein four-group of the `P ⊗ P` on the
  wires `0, 1, 2` and (276), and then this is (318)/(319) (`E336x.commBRs`).

Every step holds from five wires on (`comm344_ge5`); `eq344_5` is the case
`N = 5`.

Memory (2026-10-29): 13 s, peak 0.29 GB anonymous (3.1 GB resident with the
mapped imports).
-/
import QCert.RealCliffordCH.Sec8.D.N13.Low339

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.L344

open Circuit Eng SE Net N8 Sep L339

/-- The controls of the first multi-controlled `H` of (344). -/
abbrev cA4 (N : ℕ) (x : ℕ → Bool) (c₁ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 2 c₁) (colOn 3 N x)

/-! ## The words of `A`'s conjugation -/

/-- `S₂ P` and `P S₂` in drawn order. -/
def aL : List Lt := N13.ppL ++ [Lt.s (L.S 2)]
def aR : List Lt := [Lt.s (L.S 2)] ++ N13.ppL

theorem rt_aL : rtW aL 3 = some 2 := by decide
theorem rt_aR : rtW aR 2 = some 3 := by decide

theorem a_drop : ∀ x ∈ aL ++ aR,
    x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x ∧ x.ok 4 = true := by decide

theorem wcaR (K k : ℕ) : wc K (k + 2) aR = (pp : Circ (k + 2)) * swAt (k + 2) 2 := by
  simp only [aR, wc_append, wc_one', circS, wc_ppL']

theorem wcaL (K k : ℕ) : wc K (k + 2) aL = swAt (k + 2) 2 * (pp : Circ (k + 2)) := by
  simp only [aL, wc_append, wc_one', circS, wc_ppL']

theorem aRL (n : ℕ) (ihn : IH (n + 4)) :
    Derivable (theory (n + 4)) (wc 4 (n + 4) aR * wc 4 (n + 4) aL) 1 := by
  rw [wcaR 4 (n + 2), wcaL 4 (n + 2)]
  have e : (pp : Circ (n + 4)) * swAt (n + 4) 2 * (swAt (n + 4) 2 * pp) =
      pp * (swAt (n + 4) 2 * swAt (n + 4) 2) * pp := by simp only [mul_assoc]
  rw [e]
  exact L339.palin (pp_inv (n + 1) ihn) (swsw (n + 4) 2 (by omega))

section Frame

variable (m : ℕ) (ih : IH (m + 5))
include ih

theorem q2 : Derivable (theory (m + 5)) (swAt (m + 5) 2 * (pp : Circ (m + 5)))
    (pp * swAt (m + 5) 2) :=
  comm_low_high _ _ (lowW_pp (m + 3)) (swAt_wires (m + 5) 2).2

/-- `(P S₂) (S₂ P) = 1` and `(S₂ P) (P S₂) = 1`. -/
theorem vInv1 : Derivable (theory (m + 5))
    (((pp : Circ (m + 5)) * swAt (m + 5) 2) * (swAt (m + 5) 2 * pp)) 1 := by
  have e : ((pp : Circ (m + 5)) * swAt (m + 5) 2) * (swAt (m + 5) 2 * pp) =
      pp * (swAt (m + 5) 2 * swAt (m + 5) 2) * pp := by simp only [mul_assoc]
  rw [e]; exact L339.palin (hpp m ih) (hs m ih 2 (by omega))

theorem vInv2 : Derivable (theory (m + 5))
    ((swAt (m + 5) 2 * (pp : Circ (m + 5))) * (pp * swAt (m + 5) 2)) 1 := by
  have e : (swAt (m + 5) 2 * (pp : Circ (m + 5))) * (pp * swAt (m + 5) 2) =
      swAt (m + 5) 2 * (pp * pp) * swAt (m + 5) 2 := by simp only [mul_assoc]
  rw [e]; exact L339.palin (hs m ih 2 (by omega)) (hpp m ih)

/-- `A` as the conjugated pieces of the expansion. -/
theorem expA (x : ℕ → Bool) (c₁ : Bool) (hx : x 3 = true) :
    Derivable (theory (m + 5)) (mc (m + 5) .hg [0, 1] (cA4 (m + 5) x c₁))
      (drawn (((pcs4 true true c₁).map (cX 4 (m + 5) (xE c₁ true x))).map
        (fun a => ((pp : Circ (m + 5)) * swAt (m + 5) 2) * a * (swAt (m + 5) 2 * pp)))) := by
  have hA := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0] (colOn 1 (m + 5) (xE c₁ true x))
    (ctlOr (ctlAt 1 true) (colOn 2 (m + 5) (yP c₁ x))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [colOn, ctlOr, ctlAt, xE, yP, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  have e0 : mc (m + 5) .hg [0, 1] (cA4 (m + 5) x c₁) =
      mc (m + 5) .hg [0, 1] (colOn 2 (m + 5) (yP c₁ x)) :=
    mc_congr _ _ _ (by ctl_case)
  have hp : Derivable (theory (m + 5)) (mc (m + 5) .hg [0, 1] (colOn 2 (m + 5) (yP c₁ x)))
      ((pp : Circ (m + 5)) * bA (m + 5) (yP c₁ x) true * pp) := hg0_box4 (m + 1) (yP c₁ x)
  have ex := expX (m + 5) (by omega) ih (xE c₁ true x)
  rw [xE1, xE2, xE3] at ex
  have k1 : Derivable (theory (m + 5)) (mc (m + 5) .hg [0, 1] (cA4 (m + 5) x c₁))
      (((pp : Circ (m + 5)) * swAt (m + 5) 2) * mc (m + 5) .box [0] (colOn 1 (m + 5) (xE c₁ true x)) *
        (swAt (m + 5) 2 * pp)) := by
    rw [e0]
    refine hp.trans ((conj_eq hA.symm).trans ?_)
    simp only [mul_assoc]
    exact Derivable.refl _
  exact k1.trans ((conj_eq ex).trans (conj_drawn (vInv2 m ih) (vInv1 m ih) _))

/-! ### The pairs -/

/-- `(P S₂) Y (S₂ P) = S₂ (P Y P) S₂`-type rewriting: `(P S₂) (P Y P) (S₂ P)` is
`S₂ Y S₂`. -/
theorem conjV (Y : Circ (m + 5)) :
    Derivable (theory (m + 5))
      (((pp : Circ (m + 5)) * swAt (m + 5) 2) * (pp * Y * pp) * (swAt (m + 5) 2 * pp))
      (swAt (m + 5) 2 * Y * swAt (m + 5) 2) := by
  have h := q2 m ih
  have e : ((pp : Circ (m + 5)) * swAt (m + 5) 2) * (pp * Y * pp) * (swAt (m + 5) 2 * pp) =
      pp * (swAt (m + 5) 2 * pp) * Y * (pp * swAt (m + 5) 2) * pp := by simp only [mul_assoc]
  rw [e]
  refine (dmul (dmul (dmul (dmul (Derivable.refl _) h) (Derivable.refl Y)) h.symm)
    (Derivable.refl _)).trans ?_
  have e2 : (pp : Circ (m + 5)) * (pp * swAt (m + 5) 2) * Y * (swAt (m + 5) 2 * pp) * pp =
      (pp * pp) * (swAt (m + 5) 2 * Y * swAt (m + 5) 2) * (pp * pp) := by simp only [mul_assoc]
  rw [e2]
  have := dmul (dmul (hpp m ih) (Derivable.refl (swAt (m + 5) 2 * Y * swAt (m + 5) 2))) (hpp m ih)
  simpa only [one_mul, mul_one] using this

/-- `S₀ (P X P) S₀ = P (S₀ X S₀) P`. -/
theorem s0ppconj (X : Circ (m + 5)) :
    Derivable (theory (m + 5)) (swAt (m + 5) 0 * ((pp : Circ (m + 5)) * X * pp) * swAt (m + 5) 0)
      (pp * (swAt (m + 5) 0 * X * swAt (m + 5) 0) * pp) := by
  have hp := pp_swap4 (m + 1) ih
  have e : swAt (m + 5) 0 * ((pp : Circ (m + 5)) * X * pp) * swAt (m + 5) 0 =
      (swAt (m + 5) 0 * pp) * X * (pp * swAt (m + 5) 0) := by simp only [mul_assoc]
  rw [e]
  refine (dmul (dmul hp (Derivable.refl X)) hp.symm).trans ?_
  simp only [mul_assoc]
  exact Derivable.refl _

/-- A rotation of `A` and the remainder of `B`: (322)/(323). -/
theorem commRQ (z : ℕ → Bool) (c₁ c₂ : Bool) {r : Lt} (hr : r ∈ rots true true c₁) :
    Comm (m + 5) (((pp : Circ (m + 5)) * swAt (m + 5) 2) * r.circ 4 (m + 5) * (swAt (m + 5) 2 * pp))
      (U m * boxN (m + 5) z c₂ false * U' m) := by
  obtain ⟨one, a, β, rfl⟩ := rots_Rr hr
  have h1 := commR_ppB m ih z (!one) a c₁ β c₂
  have hs0 := hs m ih 0 (by omega)
  have sw := swapRr m (!one) a c₁ β
  rw [Bool.not_not] at sw
  have h2 := Comm.congr sw (s0ppconj m ih _)
    (Comm.conj h1 hs0 (u := swAt (m + 5) 0) (v := swAt (m + 5) 0))
  have h3 := Comm.conj h2 (vInv2 m ih) (u := (pp : Circ (m + 5)) * swAt (m + 5) 2)
    (v := swAt (m + 5) 2 * pp)
  exact Comm.congr (Derivable.refl _) ((conjV m ih _).trans (remB m ih z c₂).symm) h3

/-- The two remainders: `BoxPPBridge.commBBpp`. -/
theorem commBQ (z w : ℕ → Bool) (c₂ : Bool) :
    Comm (m + 5)
      (((pp : Circ (m + 5)) * swAt (m + 5) 2) * boxN (m + 5) z true true * (swAt (m + 5) 2 * pp))
      (U m * boxN (m + 5) w c₂ false * U' m) := by
  have h := commBBpp m ih false true true c₂ z w
  have e1 : mc (m + 5) .box [boxTarget false] (boxCtl4 (m + 5) false true true z) =
      boxN (m + 5) z true true := mc_congr _ _ _ (by unfold boxCtl4 boxCtl; ctl_eq)
  have e2 : mc (m + 5) .box [boxTarget true] (boxCtl4 (m + 5) true c₂ false w) =
      bxR (m + 5) 1 0 2 c₂ false w := mc_congr _ _ _ (by unfold boxCtl4 boxCtl; ctl_eq)
  rw [e1, e2] at h
  have h1 := Comm.congr (Derivable.refl _) (conj_eq (g4 m ih w c₂ false).symm) h
  have h3 := Comm.conj h1 (vInv2 m ih) (u := (pp : Circ (m + 5)) * swAt (m + 5) 2)
    (v := swAt (m + 5) 2 * pp)
  exact Comm.congr (Derivable.refl _) ((conjV m ih _).trans (remB m ih w c₂).symm) h3

/-- `P₀₂ X P₀₂ = X` for the box on wire `0` idle on wire `1`, as in `kR`. -/
theorem p1g (z : ℕ → Bool) (c b : Bool) :
    Derivable (theory (m + 5)) (P02 m * bxR (m + 5) 0 1 3 c b z * P02 m)
      (bxR (m + 5) 0 1 3 c b z) := by
  have hs1 := hs m ih 1 (by omega)
  have a3 := g2 m ih z c b
  have e : P02 m * bxR (m + 5) 0 1 3 c b z * P02 m = swAt (m + 5) 1 * ((pp : Circ (m + 5)) *
      (swAt (m + 5) 1 * bxR (m + 5) 0 1 3 c b z * swAt (m + 5) 1) * pp) * swAt (m + 5) 1 := by
    simp only [P02, mul_assoc]
  rw [e]
  exact (conj_eq ((conj_eq a3).trans (pp276 m ih (zR c b z)))).trans (conj_back hs1 a3)

theorem p2g (z : ℕ → Bool) (c b : Bool) :
    Derivable (theory (m + 5)) (P12 m * bxR (m + 5) 1 0 3 c b z * P12 m)
      (bxR (m + 5) 1 0 3 c b z) := by
  have hs0 := hs m ih 0 (by omega)
  have a2 := g3 m ih z c b
  have e : P12 m * bxR (m + 5) 1 0 3 c b z * P12 m = swAt (m + 5) 0 * (P02 m *
      (swAt (m + 5) 0 * bxR (m + 5) 1 0 3 c b z * swAt (m + 5) 0) * P02 m) * swAt (m + 5) 0 := by
    simp only [P12, mul_assoc]
  rw [e]
  exact (conj_eq ((conj_eq (conj_back hs0 a2)).trans (p1g m ih z c b))).trans a2

/-- `P₀₂ P₀₁ = P₁₂` and `P₀₁ P₀₂ = P₁₂`. -/
theorem klein3 : Derivable (theory (m + 5)) (P02 m * pp) (P12 m) := by
  have h := dright (pp : Circ (m + 5)) (klein2 m ih)
  refine h.trans ?_
  have e : P12 m * pp * pp = P12 m * (pp * pp) := by simp only [mul_assoc]
  rw [e]
  have := dleft (P12 m) (hpp m ih)
  simpa only [mul_one] using this

theorem klein4 : Derivable (theory (m + 5)) ((pp : Circ (m + 5)) * P02 m) (P12 m) := by
  have h := dleft (pp : Circ (m + 5)) (klein1 m ih)
  refine h.trans ?_
  have e : (pp : Circ (m + 5)) * (pp * P12 m) = (pp * pp) * P12 m := by simp only [mul_assoc]
  rw [e]
  have := dright (P12 m) (hpp m ih)
  simpa only [one_mul] using this

/-- The remainder of `A` conjugated by `U'`. -/
theorem kR2 (z : ℕ → Bool) :
    Derivable (theory (m + 5))
      (U' m * (((pp : Circ (m + 5)) * swAt (m + 5) 2) * boxN (m + 5) z true true *
        (swAt (m + 5) 2 * pp)) * U m)
      (swAt (m + 5) 0 * boxN (m + 5) z true true * swAt (m + 5) 0) := by
  have hs2 := hs m ih 2 (by omega)
  have a1 := g1 m ih z true true
  have a2 := g3 m ih z true true
  have a4 := g5 m ih z true true
  have a5 := g4 m ih z true true
  -- `S₀ (P R P) S₀ = P R2 P`
  have k0 : Derivable (theory (m + 5))
      (swAt (m + 5) 0 * ((pp : Circ (m + 5)) * (swAt (m + 5) 2 * boxN (m + 5) z true true *
        swAt (m + 5) 2) * pp) * swAt (m + 5) 0)
      ((pp : Circ (m + 5)) * bxR (m + 5) 1 0 3 true true z * pp) :=
    (s0ppconj m ih _).trans (conj_eq ((conj_eq a1).trans a2))
  have e0 : U' m * (((pp : Circ (m + 5)) * swAt (m + 5) 2) * boxN (m + 5) z true true *
        (swAt (m + 5) 2 * pp)) * U m =
      swAt (m + 5) 2 * (P02 m * (swAt (m + 5) 0 * ((pp : Circ (m + 5)) *
        (swAt (m + 5) 2 * boxN (m + 5) z true true * swAt (m + 5) 2) * pp) * swAt (m + 5) 0) *
        P02 m) * swAt (m + 5) 2 := by
    simp only [U, U', P02, mul_assoc]
  rw [e0]
  have k1 : Derivable (theory (m + 5))
      (P02 m * ((pp : Circ (m + 5)) * bxR (m + 5) 1 0 3 true true z * pp) * P02 m)
      (bxR (m + 5) 1 0 3 true true z) := by
    have e : P02 m * ((pp : Circ (m + 5)) * bxR (m + 5) 1 0 3 true true z * pp) * P02 m =
        (P02 m * pp) * bxR (m + 5) 1 0 3 true true z * (pp * P02 m) := by simp only [mul_assoc]
    rw [e]
    exact (dmul (dmul (klein3 m ih) (Derivable.refl _)) (klein4 m ih)).trans (p2g m ih z true true)
  exact (conj_eq ((conj_eq k0).trans k1)).trans ((conj_back hs2 a4).trans a5.symm)

/-- The remainder of `A` and a rotation of `B`: (318), (319) (`E336x.commBRs`). -/
theorem commBR (z : ℕ → Bool) (c₂ : Bool) {r' : Lt} (hr' : r' ∈ rots c₂ false true) :
    Comm (m + 5)
      (((pp : Circ (m + 5)) * swAt (m + 5) 2) * boxN (m + 5) z true true * (swAt (m + 5) 2 * pp))
      (U m * r'.circ 4 (m + 5) * U' m) := by
  have hs0 := hs m ih 0 (by omega)
  have h := commBRs m ih true c₂ true z hr'
  have h2 := Comm.congr (Derivable.refl _) (conj_back hs0 (Derivable.refl _))
    (Comm.conj h hs0 (u := swAt (m + 5) 0) (v := swAt (m + 5) 0))
  exact conj_comm m ih (UU' m ih) (U'U m ih) (Comm.congr (kR2 m ih z).symm (Derivable.refl _) h2)

set_option maxRecDepth 20000 in
/-- Two rotations: `(P S₂) r (S₂ P)` and `U r' U'` live on the wires `0–3`
and are trivial on complementary blocks of wire `3`. -/
theorem commRR {c₁ c₃ : Bool} {r r' : Lt} (hr : r ∈ rots true true c₁)
    (hr' : r' ∈ rots c₃ false true) :
    Comm (m + 5) (((pp : Circ (m + 5)) * swAt (m + 5) 2) * r.circ 4 (m + 5) * (swAt (m + 5) 2 * pp))
      (U m * r'.circ 4 (m + 5) * U' m) := by
  have ih4 : IH (m + 4) := ih.mono (by omega)
  have hA := rot_drop _ _ _ r hr
  have hB := rot_drop _ _ _ r' hr'
  have hu := u_drop
  have ha := a_drop
  have tA : Triv 3 0 (opsQ.eval (m + 4) (wc 4 (m + 4) (aL ++ [r] ++ aR))) := by
    rw [wc_conj]
    have hX := triv_rot (m + 4) (by omega) hr
    simp only [if_true] at hX
    exact triv_conj (K := 4) (by omega) (fun x hx => (ha x (by simp [hx])).2.2.2)
      (fun x hx => (ha x (by simp [hx])).2.2.2) (by omega) (by omega) rt_aL rt_aR
      (eval_inv (aRL m ih4)) hX
  have tB : Triv 3 1 (opsQ.eval (m + 4) (wc 4 (m + 4) (uBL ++ [r'] ++ uBR))) := by
    rw [wc_conj]
    have hX := triv_rot (m + 4) (by omega) hr'
    simp only [Bool.false_eq_true, if_false] at hX
    exact triv_conj (K := 4) (by omega) (fun x hx => (hu x (by simp [hx])).2.2.2)
      (fun x hx => (hu x (by simp [hx])).2.2.2) (by omega) (by omega) rt_uBL rt_uBR
      (eval_inv (uRL m ih4)) hX
  have hsem := sep_sem (K := 4) (M := m + 4) (by decide : (0 : Fin 2) ≠ 1) tA tB
  have mem : ∀ x ∈ (aL ++ [r] ++ aR) ++ (uBL ++ [r'] ++ uBR),
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
  have mem' : ∀ x ∈ (uBL ++ [r'] ++ uBR) ++ (aL ++ [r] ++ aR),
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := fun x hx =>
    mem x (by simp only [List.mem_append] at hx ⊢; tauto)
  have e1 : ((aL ++ [r] ++ aR) ++ (uBL ++ [r'] ++ uBR)).map (Lt.drop 4) =
      (aL ++ [r] ++ aR) ++ (uBL ++ [r'] ++ uBR) := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem x hx).2.2), List.map_id]
  have e2 : ((uBL ++ [r'] ++ uBR) ++ (aL ++ [r] ++ aR)).map (Lt.drop 4) =
      (uBL ++ [r'] ++ uBR) ++ (aL ++ [r] ++ aR) := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem' x hx).2.2), List.map_id]
  rw [← e1, ← e2] at hsem
  have hw : Derivable (theory (m + 5))
      (wc 5 (m + 5) ((aL ++ [r] ++ aR) ++ (uBL ++ [r'] ++ uBR)))
      (wc 5 (m + 5) ((uBL ++ [r'] ++ uBR) ++ (aL ++ [r] ++ aR))) :=
    SE.Frame.window (frame 4) m ih (q := 4) le_rfl
      (fun x hx => ⟨(mem x hx).1, (mem x hx).2.1⟩) (fun x hx => ⟨(mem' x hx).1, (mem' x hx).2.1⟩)
      hsem
  have eA : wc 5 (m + 5) (aL ++ [r] ++ aR) =
      ((pp : Circ (m + 5)) * swAt (m + 5) 2) * r.circ 4 (m + 5) * (swAt (m + 5) 2 * pp) := by
    rw [wc_conj, wcaR 5 (m + 3), wcaL 5 (m + 3), rots_rebase hr]
  have eB : wc 5 (m + 5) (uBL ++ [r'] ++ uBR) = U m * r'.circ 4 (m + 5) * U' m := by
    rw [wc_conj, wcU, wcU', rots_rebase hr']
  unfold Comm
  rw [drawn_two, drawn_two]
  rw [wc_append 5 (m + 5) (aL ++ [r] ++ aR) (uBL ++ [r'] ++ uBR),
    wc_append 5 (m + 5) (uBL ++ [r'] ++ uBR) (aL ++ [r] ++ aR), eA, eB] at hw
  exact hw

/-! ### The pairs and (344) -/

theorem pairs (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    ∀ a ∈ ((pcs4 true true c₁).map (cX 4 (m + 5) (xE c₁ true x))).map
        (fun a => ((pp : Circ (m + 5)) * swAt (m + 5) 2) * a * (swAt (m + 5) 2 * pp)),
      ∀ b ∈ ((pcs4 c₂ false true).map (cX 4 (m + 5) (yB c₂ y))).map
        (fun a => U m * a * U' m), Comm (m + 5) a b := by
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

/-- (344) when the colourings are black, resp. white, on wire `3`. -/
theorem core344 (x y : ℕ → Bool) (c₁ c₂ : Bool) (hx : x 3 = true) (hy : y 3 = false) :
    Comm (m + 5) (mc (m + 5) .hg [0, 1] (cA4 (m + 5) x c₁))
      (mc (m + 5) .hg [1, 2] (cB (m + 5) y c₂)) :=
  Comm.congr (expA m ih x c₁ hx).symm (expB m ih y c₂ hy).symm
    (comm_drawn _ _ (pairs m ih x y c₁ c₂))

end Frame

/-! ## Back to the interface -/

/-- (344) from five wires on. -/
theorem comm344_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₂) (colOn 3 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 5) (mc (m + 5) .hg [0, 1] (cA4 (m + 5) x c₁))
    (mc (m + 5) .hg [1, 2] (cB (m + 5) y c₂))) ?_ ?_
    (fun x y hx hy => core344 m ih x y c₁ c₂ hx hy) x y hxy
  · intro x y j hj hjN h
    have rA := swBH ih j hjN .hg (Or.inr rfl) [0, 1] [0, 1] (cA4 (m + 5) (x ∘ Net.tau j) c₁)
      (cA4 (m + 5) x c₁) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau_of_lt (show 0 < j by omega),
        Net.tau_of_lt (show 1 < j by omega)])
      (fun i hi => by
        simp only [cA4, ctlOr, ctlAt_tau (show 2 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN x hi])
    have rB := swBH ih j hjN .hg (Or.inr rfl) [1, 2] [1, 2] (cB (m + 5) (y ∘ Net.tau j) c₂)
      (cB (m + 5) y c₂) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau_of_lt (show 1 < j by omega),
        Net.tau_of_lt (show 2 < j by omega)])
      (fun i hi => by
        simp only [cB, ctlOr, ctlAt_tau (show 0 < j by omega),
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
    · have e := eq81 (m + 5) .hg [1, 2] (cB (m + 5) (flipAt 3 y) c₂) 3 (flipAt 3 y 3)
        (by omega) (by decide) (by simp [cB, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 5) 3, mc (m + 5) .hg [1, 2] (cB (m + 5) (flipAt 3 y) c₂),
          xAt (m + 5) 3] = xAt (m + 5) 3 * mc (m + 5) .hg [1, 2] (cB (m + 5) (flipAt 3 y) c₂) *
          xAt (m + 5) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 5) (by omega) y i
      simp only [cB, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all

/-- (344) on five wires, in the form of the interface `D.eq344`. -/
theorem eq344_5 (ih : IH 5) (x y : ℕ → Bool) (hxy : DiffOn 3 5 x y) (c₁ c₂ : Bool) :
    Comm 5 (mc 5 .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 5 x)))
      (mc 5 .hg [1, 2] (ctlOr (ctlAt 0 c₂) (colOn 3 5 y))) :=
  comm344_ge5 5 le_rfl ih x y hxy c₁ c₂

end QCert.RealCliffordCH.Sec8.D.N13.L344
