/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (339) from five wires on

The box `A` on wire `0` (controls `1` of colour `c₂`, `2` of colour `c₁`, the
wires `3, …` coloured by `x`) commutes with the multi-controlled `H` `B` with
its box on wire `1` and its `H` on wire `2` (control `0` of colour `c₃`, the
wires `3, …` coloured by `y`), when `x ≠ y`.

By (307), (313) and (81) the colourings may be assumed to differ on wire `3`,
black for `x` (`sep_reduce`).  The paper's frame (Appendix D.7, proof of
(339)): `A` is the swap `S₂` of the wires `2, 3` around the box of `E336x`
(`Abox`, separating control black on wire `2`, `c₁` on wire `3`), and `B` is
`U · Bbox · U'` with `U = S₀ S₁ (P ⊗ P) S₁ S₂` and `Bbox` the box of `E336x`
white on wire `2`, black on wire `3` (the `H` wire of `B`), `c₃` on wire `1`.
Both boxes are written by (320)/(321) (`expX`): rotations on the wires `0–3`
and a remainder idle on wire `3`.  The pieces commute pairwise:

* two rotations: a semantic step without wire `4`, the two being trivial on
  complementary blocks of wire `3` (`SepSem`, no simulation);
* a rotation of `A` and the remainder of `B`: the remainder conjugated by `U`
  is, through (276), the box on wire `1` idle on wire `2`, and this is
  (318)/(319) (`E336x.commRBs`) under `S₂`;
* the remainders: `E336x.commBBs` under `S₂`;
* the remainder `R` of `A` (idle on wire `2`) and a rotation of `B`
  conjugated by `U`: this is the paper's (326)/(327).  `U' R U` is `P ⊗ P`
  around the box of `E336x` conjugated by `S₀`, by the Klein four-group of
  the `P ⊗ P` on the wires `0, 1, 2` (`P₀₂ = P₀₁ P₁₂`, a three-wire identity)
  and (276) for `P₁₂` on the box wire `1` and the idle wire `2`; then it is
  (322)/(323) (`E337.commB_ppRw`).

Every step holds from five wires on (`comm339_ge5`); `eq339_5` is the case
`N = 5`.  No step decides a window in the kernel except the three-wire Klein
identities (`klein1`, `klein2`, by `Fast`).

Memory (2026-10-29): about 1 min, peak 0.69 GB anonymous (3.5 GB resident
with the mapped imports).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E337
import QCert.RealCliffordCH.Sec8.D.N13.SepSem
import QCert.RealCliffordCH.OneQubit

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.L339

open Circuit Eng SE Net N8 Sep

/-! ## Relabeling by one swap -/

/-- Naturality of boxes and multi-controlled `H` under one swap, any wires
(`E.mcSwapBH`, from (307), (313)). -/
theorem swBH {N : ℕ} (ih : IH N) (j : ℕ) (hj : j + 2 ≤ N) (K : Kind) (hK : K = .box ∨ K = .hg)
    (tg tg' : List ℕ) (c c' : ℕ → Option Bool) (htg : tg.length = kindSp K) (hnd : tg.Nodup)
    (htN : ∀ t ∈ tg, t < N) (ht' : tg.map (Net.tau j) = tg')
    (hc : ∀ i < N, c (Net.tau j i) = c' i) :
    Derivable (theory N) (swAt N j * mc N K tg c * swAt N j) (mc N K tg' c') := by
  have h := E.mcSwapBH ih j hj K hK tg c htg hnd htN
  rw [ht', show drawn [swAt N j, mc N K tg c, swAt N j] = swAt N j * mc N K tg c * swAt N j by
    simp [drawn, mul_assoc]] at h
  exact h.trans (der_of_eq (mc_congr _ _ _ hc))

/-- The colouring of a box idle on wire `1` once its controls on the wires
`2, 3` are fixed. -/
def zR (c b : Bool) (z : ℕ → Bool) : ℕ → Bool := fun i => if i = 2 then c else if i = 3 then b else z i

/-- The colouring of the box of the multi-controlled `H` on the wires `0, 1`. -/
def yP (c₃ : Bool) (y : ℕ → Bool) : ℕ → Bool := fun i => if i = 2 then c₃ else y i

/-- Pointwise equality of control functions on the wires `0, …, 4` and above. -/
macro "ctl_case" : tactic => `(tactic| (intro i hi; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨
  i = 3 ∨ i = 4 ∨ 5 ≤ i) with rfl | rfl | rfl | rfl | rfl | h5 <;>
  simp only [colOn, ctlOr, ctlAt, Net.tau, zR, yP] <;> (try split_ifs) <;>
  first | rfl | (exfalso; omega) | simp | omega))

/-! ## Small identities -/

section Small

variable {N : ℕ}

/-- `x a x` with `x` an involution and `a ≈ 1` is `≈ 1`. -/
theorem palin {x a : Circ N} (hx : Derivable (theory N) (x * x) 1)
    (ha : Derivable (theory N) a 1) : Derivable (theory N) (x * a * x) 1 :=
  (dctx x x ha).trans (by simpa only [mul_one] using hx)

/-- Conjugating an equation. -/
theorem conj_eq {u v a b : Circ N} (h : Derivable (theory N) a b) :
    Derivable (theory N) (u * a * v) (u * b * v) := dctx u v h

/-- Two conjugations compose. -/
theorem conj_trans {u v w w' a b c : Circ N} (h1 : Derivable (theory N) (u * a * v) b)
    (h2 : Derivable (theory N) (w * b * w') c) :
    Derivable (theory N) ((w * u) * a * (v * w')) c := by
  have e : (w * u) * a * (v * w') = w * (u * a * v) * w' := by simp only [mul_assoc]
  rw [e]; exact (dctx w w' h1).trans h2

end Small

/-- `P ⊗ P` on the wires `0, 1` from the width-`(k + 2)` placement. -/
theorem ppAt01 (k : ℕ) : ppAt (k + 2) 0 1 = (pp : Circ (k + 2)) := by
  rw [← N8.atBot_pp (k + 2) k le_rfl, atBot_self]

/-! ## The colourings and the gates -/

/-- The colours of the box of `A` in the frame of `E336x`. -/
def xE (c₁ c₂ : Bool) (x : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 1 then c₂ else if i = 2 then true else if i = 3 then c₁ else x i

/-- The colours of the box inside `B`. -/
def yB (c₃ : Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 1 then c₃ else if i = 2 then false else if i = 3 then true else y i

theorem xE1 (c₁ c₂ : Bool) (x : ℕ → Bool) : xE c₁ c₂ x 1 = c₂ := by simp [xE]
theorem xE2 (c₁ c₂ : Bool) (x : ℕ → Bool) : xE c₁ c₂ x 2 = true := by simp [xE]
theorem xE3 (c₁ c₂ : Bool) (x : ℕ → Bool) : xE c₁ c₂ x 3 = c₁ := by simp [xE]
theorem yB1 (c₃ : Bool) (y : ℕ → Bool) : yB c₃ y 1 = c₃ := by simp [yB]
theorem yB2 (c₃ : Bool) (y : ℕ → Bool) : yB c₃ y 2 = false := by simp [yB]
theorem yB3 (c₃ : Bool) (y : ℕ → Bool) : yB c₃ y 3 = true := by simp [yB]

/-- The controls of the box of (339). -/
abbrev cA (N : ℕ) (x : ℕ → Bool) (c₁ c₂ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))
/-- The controls of the multi-controlled `H` of (339). -/
abbrev cB (N : ℕ) (y : ℕ → Bool) (c₃ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 0 c₃) (colOn 3 N y)

/-- The conjugating word of `B`: `S₀ S₁ (P ⊗ P) S₁ S₂`, and its reverse. -/
abbrev U (m : ℕ) : Circ (m + 5) :=
  swAt (m + 5) 0 * swAt (m + 5) 1 * (pp : Circ (m + 5)) * swAt (m + 5) 1 * swAt (m + 5) 2
abbrev U' (m : ℕ) : Circ (m + 5) :=
  swAt (m + 5) 2 * swAt (m + 5) 1 * (pp : Circ (m + 5)) * swAt (m + 5) 1 * swAt (m + 5) 0

/-- A box on wire `t` with controls `j`, `k` and the wires `4, …`. -/
abbrev bxR (N t j k : ℕ) (cj ck : Bool) (z : ℕ → Bool) : Circ N :=
  mc N .box [t] (ctlOr (ctlAt j cj) (ctlOr (ctlAt k ck) (colOn 4 N z)))

theorem ppAt5 (m : ℕ) : ppAt (m + 5) 0 1 = (pp : Circ (m + 5)) := ppAt01 (m + 3)

/-- `P ⊗ P` on the wires `0, 2` and `1, 2`. -/
abbrev P02 (m : ℕ) : Circ (m + 5) := swAt (m + 5) 1 * pp * swAt (m + 5) 1
abbrev P12 (m : ℕ) : Circ (m + 5) := swAt (m + 5) 0 * P02 m * swAt (m + 5) 0

/-! ## Words for the semantic steps -/

/-- The words of `U'` and `U` in drawn order. -/
def uBL : List Lt := [.s (.S 0), .s (.S 1)] ++ N13.ppL ++ [.s (.S 1), .s (.S 2)]
def uBR : List Lt := [.s (.S 2), .s (.S 1)] ++ N13.ppL ++ [.s (.S 1), .s (.S 0)]

theorem circS (K N j : ℕ) : (Lt.s (L.S j)).circ K N = swAt N j := rfl

theorem wc_conj (K N : ℕ) (u u' : List Lt) (h : Lt) :
    wc K N (u ++ [h] ++ u') = wc K N u' * h.circ K N * wc K N u := by
  rw [wc_append, wc_append]
  simp [wc, drawn, mul_assoc]

theorem wc_ppL' (K k : ℕ) : wc K (k + 2) N13.ppL = (pp : Circ (k + 2)) := rfl

theorem wcR (K k : ℕ) : wc K (k + 2) uBR =
    swAt (k + 2) 0 * swAt (k + 2) 1 * (pp : Circ (k + 2)) * swAt (k + 2) 1 * swAt (k + 2) 2 := by
  simp only [uBR, wc_append, wc_two, drawn_two, circS, wc_ppL', mul_assoc]

theorem wcL (K k : ℕ) : wc K (k + 2) uBL =
    swAt (k + 2) 2 * swAt (k + 2) 1 * (pp : Circ (k + 2)) * swAt (k + 2) 1 * swAt (k + 2) 0 := by
  simp only [uBL, wc_append, wc_two, drawn_two, circS, wc_ppL', mul_assoc]

theorem wcU (K m : ℕ) : wc K (m + 5) uBR = U m := wcR K (m + 3)
theorem wcU' (K m : ℕ) : wc K (m + 5) uBL = U' m := wcL K (m + 3)

/-- `U U' = 1` one wire down. -/
theorem uRL (n : ℕ) (ihn : IH (n + 4)) :
    Derivable (theory (n + 4)) (wc 4 (n + 4) uBR * wc 4 (n + 4) uBL) 1 := by
  rw [wcR 4 (n + 2), wcL 4 (n + 2)]
  have e : swAt (n + 4) 0 * swAt (n + 4) 1 * (pp : Circ (n + 4)) * swAt (n + 4) 1 * swAt (n + 4) 2 *
      (swAt (n + 4) 2 * swAt (n + 4) 1 * (pp : Circ (n + 4)) * swAt (n + 4) 1 * swAt (n + 4) 0) =
      swAt (n + 4) 0 * (swAt (n + 4) 1 * ((pp : Circ (n + 4)) * (swAt (n + 4) 1 *
        (swAt (n + 4) 2 * swAt (n + 4) 2) * swAt (n + 4) 1) * pp) * swAt (n + 4) 1) *
        swAt (n + 4) 0 := by simp only [mul_assoc]
  rw [e]
  exact palin (swsw (n + 4) 0 (by omega)) (palin (swsw (n + 4) 1 (by omega))
    (palin (pp_inv (n + 1) ihn) (palin (swsw (n + 4) 1 (by omega)) (swsw (n + 4) 2 (by omega)))))

theorem triv_rot (M : ℕ) (hM : 4 ≤ M) {b1 b2 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 b2 b3) :
    Triv 2 (if b2 then 0 else 1) (opsQ.eval M (r.circ 4 M)) := by
  have hok : r.ok 4 = true := by
    simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> cases b1 <;> rfl
  obtain ⟨Kd, tg, cs, bb, rfl, hl, ht⟩ : ∃ Kd tg cs bb, r = Lt.g Kd tg cs bb ∧
      cs.lookup 2 = some b2 ∧ 2 ∉ tg := by
    simp only [rots, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, _, rfl, rfl, by decide⟩
  exact triv_g (K := 4) hM Kd tg cs bb hok (by omega) ht hl

theorem rot_drop : ∀ b1 b2 b3 : Bool, ∀ r ∈ rots b1 b2 b3,
    r.ok 5 = true ∧ r.avoids 4 = true ∧ r.drop 4 = r ∧ r.ok 4 = true := by decide

theorem u_drop : ∀ x ∈ uBL ++ uBR ++ [.s (.S 2)],
    x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x ∧ x.ok 4 = true := by decide

theorem rt_uBL : rtW uBL 3 = some 2 := by decide
theorem rt_uBR : rtW uBR 2 = some 3 := by decide
theorem rt_S2 : rtW [.s (.S 2)] 3 = some 2 := by decide
theorem rt_S2' : rtW [.s (.S 2)] 2 = some 3 := by decide

theorem eval_inv {M : ℕ} {a b : Circ M} (h : Derivable (theory M) (a * b) 1) :
    opsQ.eval M a * opsQ.eval M b = 1 := by
  have := eval_eq_of_sem (sem_of_derivable h)
  rwa [map_mul, map_one] at this

section Frame

variable (m : ℕ) (ih : IH (m + 5))
include ih

theorem hs (j : ℕ) (hj : j ≤ 3) : Derivable (theory (m + 5)) (swAt (m + 5) j * swAt (m + 5) j) 1 :=
  swsw (m + 5) j (by omega)

theorem hpp : Derivable (theory (m + 5)) ((pp : Circ (m + 5)) * pp) 1 := pp5_inv m ih

theorem UU' : Derivable (theory (m + 5)) (U m * U' m) 1 := by
  have e : U m * U' m = swAt (m + 5) 0 * (swAt (m + 5) 1 * (pp * (swAt (m + 5) 1 *
      (swAt (m + 5) 2 * swAt (m + 5) 2) * swAt (m + 5) 1) * pp) * swAt (m + 5) 1) *
      swAt (m + 5) 0 := by simp only [U, U', mul_assoc]
  rw [e]
  exact palin (hs m ih 0 (by omega)) (palin (hs m ih 1 (by omega)) (palin (hpp m ih)
    (palin (hs m ih 1 (by omega)) (hs m ih 2 (by omega)))))

theorem U'U : Derivable (theory (m + 5)) (U' m * U m) 1 := by
  have e : U' m * U m = swAt (m + 5) 2 * (swAt (m + 5) 1 * (pp * (swAt (m + 5) 1 *
      (swAt (m + 5) 0 * swAt (m + 5) 0) * swAt (m + 5) 1) * pp) * swAt (m + 5) 1) *
      swAt (m + 5) 2 := by simp only [U, U', mul_assoc]
  rw [e]
  exact palin (hs m ih 2 (by omega)) (palin (hs m ih 1 (by omega)) (palin (hpp m ih)
    (palin (hs m ih 1 (by omega)) (hs m ih 0 (by omega)))))

/-! ### `A` -/

/-- `A` as the conjugated pieces of the expansion. -/
theorem expA (x : ℕ → Bool) (c₁ c₂ : Bool) (hx : x 3 = true) :
    Derivable (theory (m + 5)) (mc (m + 5) .box [0] (cA (m + 5) x c₁ c₂))
      (drawn (((pcs4 c₂ true c₁).map (cX 4 (m + 5) (xE c₁ c₂ x))).map
        (fun a => swAt (m + 5) 2 * a * swAt (m + 5) 2))) := by
  have hA := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0] (colOn 1 (m + 5) (xE c₁ c₂ x))
    (cA (m + 5) x c₁ c₂) rfl (by decide) (by intro t ht; simp at ht; omega) rfl (by
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cA, colOn, ctlOr, ctlAt, xE, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  have ex := expX (m + 5) (by omega) ih (xE c₁ c₂ x)
  rw [xE1, xE2, xE3] at ex
  have h2 := hs m ih 2 (by omega)
  exact hA.symm.trans ((conj_eq ex).trans (conj_drawn h2 h2 _))

/-! ### `B` -/

/-- `B` as `U · Bbox · U'`. -/
theorem hgU (y : ℕ → Bool) (c₃ : Bool) (hy : y 3 = false) :
    Derivable (theory (m + 5)) (mc (m + 5) .hg [1, 2] (cB (m + 5) y c₃))
      (U m * mc (m + 5) .box [0] (colOn 1 (m + 5) (yB c₃ y)) * U' m) := by
  have s0 := swBH ih 0 (by omega) .hg (Or.inr rfl) [0, 2] [1, 2]
    (ctlOr (ctlAt 1 c₃) (colOn 3 (m + 5) y)) (cB (m + 5) y c₃) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have s1 := swBH ih 1 (by omega) .hg (Or.inr rfl) [0, 1] [0, 2]
    (colOn 2 (m + 5) (yP c₃ y)) (ctlOr (ctlAt 1 c₃) (colOn 3 (m + 5) y)) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have hp : Derivable (theory (m + 5)) (mc (m + 5) .hg [0, 1] (colOn 2 (m + 5) (yP c₃ y)))
      ((pp : Circ (m + 5)) * bA (m + 5) (yP c₃ y) true * pp) := hg0_box4 (m + 1) (yP c₃ y)
  have t1 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 true) (colOn 3 (m + 5) y)))
    (ctlOr (ctlAt 1 true) (colOn 2 (m + 5) (yP c₃ y))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)
  have t2 := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0] (colOn 1 (m + 5) (yB c₃ y))
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 true) (colOn 3 (m + 5) y))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [colOn, ctlOr, ctlAt, yB, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  have k1 := hp.trans (dctx _ _ (t1.symm.trans (dctx _ _ t2.symm)))
  have k2 := s0.symm.trans (dctx _ _ (s1.symm.trans (dctx _ _ k1)))
  have e : swAt (m + 5) 0 * (swAt (m + 5) 1 * ((pp : Circ (m + 5)) * (swAt (m + 5) 1 *
      (swAt (m + 5) 2 * mc (m + 5) .box [0] (colOn 1 (m + 5) (yB c₃ y)) * swAt (m + 5) 2) *
      swAt (m + 5) 1) * pp) * swAt (m + 5) 1) * swAt (m + 5) 0 =
      U m * mc (m + 5) .box [0] (colOn 1 (m + 5) (yB c₃ y)) * U' m := by
    simp only [U, U', mul_assoc]
  rw [e] at k2
  exact k2

/-- `B` as the conjugated pieces of the expansion. -/
theorem expB (y : ℕ → Bool) (c₃ : Bool) (hy : y 3 = false) :
    Derivable (theory (m + 5)) (mc (m + 5) .hg [1, 2] (cB (m + 5) y c₃))
      (drawn (((pcs4 c₃ false true).map (cX 4 (m + 5) (yB c₃ y))).map
        (fun a => U m * a * U' m))) := by
  have ex := expX (m + 5) (by omega) ih (yB c₃ y)
  rw [yB1, yB2, yB3] at ex
  exact (hgU m ih y c₃ hy).trans ((conj_eq ex).trans (conj_drawn (U'U m ih) (UU' m ih) _))

/-! ### (276) on the box wire `0` and the idle wire `1` -/

/-- (276) for the box on wire `0`, wire `1` idle, the wires `2, …` coloured
by `z`: `N8.s276` (box wire `1`, wire `0` idle) read on two local wires,
coloured, and conjugated by the swap of the wires `0, 1`. -/
theorem pp276 (z : ℕ → Bool) :
    Derivable (theory (m + 5))
      ((pp : Circ (m + 5)) * mc (m + 5) .box [0] (colOn 2 (m + 5) z) * pp)
      (mc (m + 5) .box [0] (colOn 2 (m + 5) z)) := by
  have h0 : Derivable (theory (m + 5)) (wc 5 (m + 5) (N8.ppL 0 ++ [B1] ++ N8.ppL 0))
      (wc 5 (m + 5) [B1]) := s276 m ih
  rw [B1_eq] at h0
  have eB : (Lt.g .box [1] [(2, true), (3, true), (4, true)] true).circ 5 (m + 5) =
      (Lt.g .box [1] [] true).circ 2 (m + 5) :=
    mc_congr _ _ _ (by ctl_tac)
  have ep : ∀ K, wc K (m + 5) (N8.ppL 0) = (pp : Circ (m + 5)) := fun _ => rfl
  have h2 : Derivable (theory (m + 5))
      (wc 2 (m + 5) (N8.ppL 0 ++ [Lt.g .box [1] [] true] ++ N8.ppL 0))
      (wc 2 (m + 5) [Lt.g .box [1] [] true]) := by
    simp only [wc_append, wc_one', ep] at h0 ⊢
    rwa [eB] at h0
  have hc := colour_wc (K := 2) (N := m + 5) (by omega) z
    (l := N8.ppL 0 ++ [Lt.g .box [1] [] true] ++ N8.ppL 0)
    (r := [Lt.g .box [1] [] true]) (by decide) (by decide) h2
  have eY : cX 2 (m + 5) z (Lt.g .box [1] [] true) =
      mc (m + 5) .box [1] (colOn 2 (m + 5) z) := by
    show mc _ _ _ _ = _
    refine mc_congr _ _ _ (fun i hi => ?_)
    simp only [ctlX, colOn]
    split_ifs <;> first | rfl | omega
  have eL : wcX 2 (m + 5) z (N8.ppL 0 ++ [Lt.g .box [1] [] true] ++ N8.ppL 0) =
      (pp : Circ (m + 5)) * mc (m + 5) .box [1] (colOn 2 (m + 5) z) * pp := by
    unfold wcX
    simp only [List.map_append, drawn_append, List.map_singleton, drawn_one, eY]
    rfl
  have eR : wcX 2 (m + 5) z [Lt.g .box [1] [] true] =
      mc (m + 5) .box [1] (colOn 2 (m + 5) z) := by
    unfold wcX
    rw [List.map_singleton, drawn_one, eY]
  rw [eL, eR] at hc
  have eS := swBH ih 0 (by omega) .box (Or.inl rfl) [1] [0] (colOn 2 (m + 5) z)
    (colOn 2 (m + 5) z) rfl (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases i with _ | _ | i <;> simp [colOn, Net.tau])
  have hp := pp_swap4 (m + 1) ih
  exact (pp_move_swap hp eS).symm.trans ((dctx _ _ hc).trans eS)

/-! ### Relabelings of the boxes idle on one wire -/

theorem g1 (z : ℕ → Bool) (c b : Bool) : Derivable (theory (m + 5))
    (swAt (m + 5) 2 * bxR (m + 5) 0 1 2 c b z * swAt (m + 5) 2) (bxR (m + 5) 0 1 3 c b z) :=
  swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0] _ _ rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)

theorem g2 (z : ℕ → Bool) (c b : Bool) : Derivable (theory (m + 5))
    (swAt (m + 5) 1 * bxR (m + 5) 0 1 3 c b z * swAt (m + 5) 1)
    (mc (m + 5) .box [0] (colOn 2 (m + 5) (zR c b z))) :=
  swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0] _ _ rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)

theorem g3 (z : ℕ → Bool) (c b : Bool) : Derivable (theory (m + 5))
    (swAt (m + 5) 0 * bxR (m + 5) 0 1 3 c b z * swAt (m + 5) 0) (bxR (m + 5) 1 0 3 c b z) :=
  swBH ih 0 (by omega) .box (Or.inl rfl) [0] [1] _ _ rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)

theorem g4 (z : ℕ → Bool) (c b : Bool) : Derivable (theory (m + 5))
    (swAt (m + 5) 0 * bxR (m + 5) 0 1 2 c b z * swAt (m + 5) 0) (bxR (m + 5) 1 0 2 c b z) :=
  swBH ih 0 (by omega) .box (Or.inl rfl) [0] [1] _ _ rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)

theorem g5 (z : ℕ → Bool) (c b : Bool) : Derivable (theory (m + 5))
    (swAt (m + 5) 2 * bxR (m + 5) 1 0 2 c b z * swAt (m + 5) 2) (bxR (m + 5) 1 0 3 c b z) :=
  swBH ih 2 (by omega) .box (Or.inl rfl) [1] [1] _ _ rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case)

/-! ### The remainder of `B` conjugated by `U` -/

/-- The remainder of `B`, conjugated by `U`, is the box on wire `1` idle on
wire `2`; so is `S₂ S₀ X S₀ S₂`. -/
theorem remB (z : ℕ → Bool) (c₃ : Bool) :
    Derivable (theory (m + 5)) (U m * boxN (m + 5) z c₃ false * U' m)
      (swAt (m + 5) 2 * (swAt (m + 5) 0 * boxN (m + 5) z c₃ false * swAt (m + 5) 0) *
        swAt (m + 5) 2) := by
  have a1 := g1 m ih z c₃ false
  have a2 := g2 m ih z c₃ false
  have a3 := pp276 m ih (zR c₃ false z)
  have a4 := g3 m ih z c₃ false
  have b1 := g4 m ih z c₃ false
  have b2 := g5 m ih z c₃ false
  have hs1 := hs m ih 1 (by omega)
  have l1 : Derivable (theory (m + 5))
      (swAt (m + 5) 1 * ((pp : Circ (m + 5)) * (swAt (m + 5) 1 * (swAt (m + 5) 2 *
        bxR (m + 5) 0 1 2 c₃ false z * swAt (m + 5) 2) * swAt (m + 5) 1) * pp) * swAt (m + 5) 1)
      (bxR (m + 5) 0 1 3 c₃ false z) :=
    (conj_eq ((conj_eq ((conj_eq a1).trans a2)).trans a3)).trans (conj_back hs1 a2)
  have l2 : Derivable (theory (m + 5))
      (swAt (m + 5) 0 * (swAt (m + 5) 1 * ((pp : Circ (m + 5)) * (swAt (m + 5) 1 *
        (swAt (m + 5) 2 * bxR (m + 5) 0 1 2 c₃ false z * swAt (m + 5) 2) * swAt (m + 5) 1) *
        pp) * swAt (m + 5) 1) * swAt (m + 5) 0)
      (bxR (m + 5) 1 0 3 c₃ false z) :=
    (conj_eq l1).trans a4
  have l3 : Derivable (theory (m + 5))
      (swAt (m + 5) 2 * (swAt (m + 5) 0 * bxR (m + 5) 0 1 2 c₃ false z * swAt (m + 5) 0) *
        swAt (m + 5) 2) (bxR (m + 5) 1 0 3 c₃ false z) :=
    (conj_eq b1).trans b2
  have e : swAt (m + 5) 0 * (swAt (m + 5) 1 * ((pp : Circ (m + 5)) * (swAt (m + 5) 1 *
      (swAt (m + 5) 2 * bxR (m + 5) 0 1 2 c₃ false z * swAt (m + 5) 2) * swAt (m + 5) 1) * pp) *
      swAt (m + 5) 1) * swAt (m + 5) 0 = U m * boxN (m + 5) z c₃ false * U' m := by
    simp only [U, U', mul_assoc]
  rw [e] at l2
  exact l2.trans l3.symm

/-! ### The Klein four-group of `P ⊗ P` on three wires -/

/-- `P₀₂ = P₀₁ P₁₂`, a three-wire identity. -/
theorem klein1 : Derivable (theory (m + 5)) (P02 m) (pp * P12 m) := by
  have h3 : Derivable (theory 3) (swAt 3 1 * (pp : Circ 3) * swAt 3 1)
      ((pp : Circ 3) * (swAt 3 0 * (swAt 3 1 * pp * swAt 3 1) * swAt 3 0)) :=
    ih 3 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  have h := der_atBot h3 (m + 5) (by omega)
  simp only [atBot_mul, atBot_swAt (m := 3) 0 (by omega) (m + 5) (by omega),
    atBot_swAt (m := 3) 1 (by omega) (m + 5) (by omega), N8.atBot_pp (m + 5) 1 (by omega), ppAt5] at h
  exact h

/-- `P₀₂ = P₁₂ P₀₁`. -/
theorem klein2 : Derivable (theory (m + 5)) (P02 m) (P12 m * pp) := by
  have h3 : Derivable (theory 3) (swAt 3 1 * (pp : Circ 3) * swAt 3 1)
      ((swAt 3 0 * (swAt 3 1 * pp * swAt 3 1) * swAt 3 0) * (pp : Circ 3)) :=
    ih 3 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  have h := der_atBot h3 (m + 5) (by omega)
  simp only [atBot_mul, atBot_swAt (m := 3) 0 (by omega) (m + 5) (by omega),
    atBot_swAt (m := 3) 1 (by omega) (m + 5) (by omega), N8.atBot_pp (m + 5) 1 (by omega), ppAt5] at h
  exact h

/-- The remainder `S₂ X S₂` of `A` conjugated by `U'`: `P ⊗ P` around `X`,
conjugated by `S₀` (the step of the paper's proofs of (326), (327)). -/
theorem kR (z : ℕ → Bool) (c₂ : Bool) :
    Derivable (theory (m + 5))
      (U' m * (swAt (m + 5) 2 * boxN (m + 5) z c₂ true * swAt (m + 5) 2) * U m)
      (swAt (m + 5) 0 * ((pp : Circ (m + 5)) * boxN (m + 5) z c₂ true * pp) * swAt (m + 5) 0) := by
  have hs0 := hs m ih 0 (by omega)
  have hs1 := hs m ih 1 (by omega)
  have hs2 := hs m ih 2 (by omega)
  have a1 := g1 m ih z c₂ true
  have a2 := g3 m ih z c₂ true
  have a3 := g2 m ih z c₂ true
  -- `P₀₂ (bxR (m + 5) 0 1 3 c₂ true z) P₀₂ = (bxR (m + 5) 0 1 3 c₂ true z)`: (276) between the swaps of the wires `1, 2`
  have p1 : Derivable (theory (m + 5)) (P02 m * (bxR (m + 5) 0 1 3 c₂ true z) * P02 m) (bxR (m + 5) 0 1 3 c₂ true z) := by
    have e : P02 m * (bxR (m + 5) 0 1 3 c₂ true z) * P02 m = swAt (m + 5) 1 * ((pp : Circ (m + 5)) *
        (swAt (m + 5) 1 * (bxR (m + 5) 0 1 3 c₂ true z) * swAt (m + 5) 1) * pp) * swAt (m + 5) 1 := by
      simp only [P02, mul_assoc]
    rw [e]
    exact (conj_eq ((conj_eq a3).trans (pp276 m ih (zR c₂ true z)))).trans (conj_back hs1 a3)
  -- `P₁₂ (bxR (m + 5) 1 0 3 c₂ true z) P₁₂ = (bxR (m + 5) 1 0 3 c₂ true z)`
  have p2 : Derivable (theory (m + 5)) (P12 m * (bxR (m + 5) 1 0 3 c₂ true z) * P12 m) (bxR (m + 5) 1 0 3 c₂ true z) := by
    have e : P12 m * (bxR (m + 5) 1 0 3 c₂ true z) * P12 m = swAt (m + 5) 0 * (P02 m * (swAt (m + 5) 0 * (bxR (m + 5) 1 0 3 c₂ true z) *
        swAt (m + 5) 0) * P02 m) * swAt (m + 5) 0 := by
      simp only [P12, mul_assoc]
    rw [e]
    exact (conj_eq ((conj_eq (conj_back hs0 a2)).trans p1)).trans a2
  -- `P₀₂ (bxR (m + 5) 1 0 3 c₂ true z) P₀₂ = P₀₁ (bxR (m + 5) 1 0 3 c₂ true z) P₀₁`
  have p3 : Derivable (theory (m + 5)) (P02 m * (bxR (m + 5) 1 0 3 c₂ true z) * P02 m) ((pp : Circ (m + 5)) * (bxR (m + 5) 1 0 3 c₂ true z) * pp) := by
    refine (dmul (dmul (klein1 m ih) (Derivable.refl (bxR (m + 5) 1 0 3 c₂ true z))) (klein2 m ih)).trans ?_
    have e : (pp : Circ (m + 5)) * P12 m * (bxR (m + 5) 1 0 3 c₂ true z) * (P12 m * pp) =
        pp * (P12 m * (bxR (m + 5) 1 0 3 c₂ true z) * P12 m) * pp := by
      simp only [mul_assoc]
    rw [e]
    exact conj_eq p2
  -- `S₂` passes `P ⊗ P`
  have q2 : Derivable (theory (m + 5)) (swAt (m + 5) 2 * (pp : Circ (m + 5)))
      (pp * swAt (m + 5) 2) :=
    comm_low_high _ _ (lowW_pp (m + 3)) (swAt_wires (m + 5) 2).2
  have a4 := g5 m ih z c₂ true
  have a5 := g4 m ih z c₂ true
  have e0 : U' m * (swAt (m + 5) 2 * boxN (m + 5) z c₂ true * swAt (m + 5) 2) * U m =
      swAt (m + 5) 2 * (P02 m * (swAt (m + 5) 0 * (swAt (m + 5) 2 * boxN (m + 5) z c₂ true *
        swAt (m + 5) 2) * swAt (m + 5) 0) * P02 m) * swAt (m + 5) 2 := by
    simp only [U, U', P02, mul_assoc]
  rw [e0]
  have k1 : Derivable (theory (m + 5))
      (swAt (m + 5) 2 * (P02 m * (swAt (m + 5) 0 * (swAt (m + 5) 2 * boxN (m + 5) z c₂ true *
        swAt (m + 5) 2) * swAt (m + 5) 0) * P02 m) * swAt (m + 5) 2)
      (swAt (m + 5) 2 * ((pp : Circ (m + 5)) * (bxR (m + 5) 1 0 3 c₂ true z) * pp) * swAt (m + 5) 2) :=
    conj_eq ((conj_eq ((conj_eq a1).trans a2)).trans p3)
  have k2 : Derivable (theory (m + 5))
      (swAt (m + 5) 2 * ((pp : Circ (m + 5)) * (bxR (m + 5) 1 0 3 c₂ true z) * pp) * swAt (m + 5) 2)
      ((pp : Circ (m + 5)) * (bxR (m + 5) 1 0 2 c₂ true z) * pp) := by
    have e : swAt (m + 5) 2 * ((pp : Circ (m + 5)) * (bxR (m + 5) 1 0 3 c₂ true z) * pp) * swAt (m + 5) 2 =
        (swAt (m + 5) 2 * pp) * (bxR (m + 5) 1 0 3 c₂ true z) * (pp * swAt (m + 5) 2) := by simp only [mul_assoc]
    rw [e]
    refine (dmul (dmul q2 (Derivable.refl (bxR (m + 5) 1 0 3 c₂ true z))) q2.symm).trans ?_
    have e2 : (pp : Circ (m + 5)) * swAt (m + 5) 2 * (bxR (m + 5) 1 0 3 c₂ true z) * (swAt (m + 5) 2 * pp) =
        pp * (swAt (m + 5) 2 * (bxR (m + 5) 1 0 3 c₂ true z) * swAt (m + 5) 2) * pp := by simp only [mul_assoc]
    rw [e2]
    exact conj_eq (conj_back hs2 a4)
  have k3 : Derivable (theory (m + 5)) ((pp : Circ (m + 5)) * (bxR (m + 5) 1 0 2 c₂ true z) * pp)
      (swAt (m + 5) 0 * ((pp : Circ (m + 5)) * boxN (m + 5) z c₂ true * pp) *
        swAt (m + 5) 0) := by
    have hp := pp_swap4 (m + 1) ih
    refine (conj_eq a5.symm).trans ?_
    have e : (pp : Circ (m + 5)) * (swAt (m + 5) 0 * boxN (m + 5) z c₂ true * swAt (m + 5) 0) *
        pp = (pp * swAt (m + 5) 0) * boxN (m + 5) z c₂ true * (swAt (m + 5) 0 * pp) := by
      simp only [mul_assoc]
    rw [e]
    refine (dmul (dmul hp.symm (Derivable.refl _)) hp).trans ?_
    simp only [mul_assoc]
    exact Derivable.refl _
  exact k1.trans (k2.trans k3)

/-! ### The pairs -/

theorem conj_comm {u v a b : Circ (m + 5)} (huv : Derivable (theory (m + 5)) (u * v) 1)
    (hvu : Derivable (theory (m + 5)) (v * u) 1) (h : Comm (m + 5) (v * a * u) b) :
    Comm (m + 5) a (u * b * v) := by
  have h' := Comm.conj h hvu (u := u) (v := v)
  refine Comm.congr ?_ (Derivable.refl _) h'
  have e : u * (v * a * u) * v = (u * v) * a * (u * v) := by simp only [mul_assoc]
  rw [e]
  have := dmul (dmul huv (Derivable.refl a)) huv
  simpa only [one_mul, mul_one] using this

/-- The remainder of `A` and a rotation of `B` conjugated by `U`: the
paper's (326), (327). -/
theorem commBR (z : ℕ → Bool) (c₂ c₃ : Bool) {r' : Lt} (hr' : r' ∈ rots c₃ false true) :
    Comm (m + 5) (swAt (m + 5) 2 * boxN (m + 5) z c₂ true * swAt (m + 5) 2)
      (U m * r'.circ 4 (m + 5) * U' m) := by
  obtain ⟨r'', hr'', hsr⟩ := s0_rots (m + 5) (by omega) hr'
  obtain ⟨one, a, β, rfl⟩ := srots_Rw hr''
  have hs0 := hs m ih 0 (by omega)
  have h1 := commB_ppRw m ih z c₂ one a true β
  have h2 := Comm.congr (Derivable.refl _) (pp_pp_conj ih _)
    (Comm.conj h1 (hpp m ih) (u := pp) (v := pp))
  have h3 := Comm.congr (Derivable.refl _) (conj_back hs0 hsr)
    (Comm.conj h2 hs0 (u := swAt (m + 5) 0) (v := swAt (m + 5) 0))
  exact conj_comm m ih (UU' m ih) (U'U m ih) (Comm.congr (kR m ih z c₂).symm (Derivable.refl _) h3)

/-- A rotation of `A` and the remainder of `B`: (318), (319) under `S₂`. -/
theorem commRQ (z : ℕ → Bool) (c₁ c₂ c₃ : Bool) {r : Lt} (hr : r ∈ rots c₂ true c₁) :
    Comm (m + 5) (swAt (m + 5) 2 * r.circ 4 (m + 5) * swAt (m + 5) 2)
      (U m * boxN (m + 5) z c₃ false * U' m) := by
  have h := commRBs m ih c₂ c₁ c₃ z hr
  exact Comm.congr (Derivable.refl _) (remB m ih z c₃).symm
    (Comm.conj h (hs m ih 2 (by omega)) (u := swAt (m + 5) 2) (v := swAt (m + 5) 2))

/-- The two remainders: `E336x.commBBs` under `S₂`. -/
theorem commBQ (z w : ℕ → Bool) (c₂ c₃ : Bool) :
    Comm (m + 5) (swAt (m + 5) 2 * boxN (m + 5) z c₂ true * swAt (m + 5) 2)
      (U m * boxN (m + 5) w c₃ false * U' m) := by
  have h := commBBs m ih c₂ c₃ z w
  exact Comm.congr (Derivable.refl _) (remB m ih w c₃).symm
    (Comm.conj h (hs m ih 2 (by omega)) (u := swAt (m + 5) 2) (v := swAt (m + 5) 2))

/-! ### Two rotations: separated on wire `3`, a semantic step without wire `4` -/

set_option maxRecDepth 20000 in
/-- The two words, `S₂ r S₂` and `U r' U'`, commute: they live on the wires
`0–3` and are trivial on complementary blocks of wire `3`. -/
theorem commRR {c₁ c₂ c₃ : Bool} {r r' : Lt} (hr : r ∈ rots c₂ true c₁)
    (hr' : r' ∈ rots c₃ false true) :
    Comm (m + 5) (swAt (m + 5) 2 * r.circ 4 (m + 5) * swAt (m + 5) 2)
      (U m * r'.circ 4 (m + 5) * U' m) := by
  have ih4 : IH (m + 4) := ih.mono (by omega)
  have hA := rot_drop _ _ _ r hr
  have hB := rot_drop _ _ _ r' hr'
  have hu := u_drop
  -- the semantics one wire down
  have tA : Triv 3 0 (opsQ.eval (m + 4) (wc 4 (m + 4) ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]))) := by
    rw [wc_conj]
    have hX := triv_rot (m + 4) (by omega) hr
    simp only [if_true] at hX
    have hinv : opsQ.eval (m + 4) (wc 4 (m + 4) [Lt.s (L.S 2)]) *
        opsQ.eval (m + 4) (wc 4 (m + 4) [Lt.s (L.S 2)]) = 1 := by
      rw [wc_one', circS]; exact eval_inv (swsw (m + 4) 2 (by omega))
    exact triv_conj (K := 4) (by omega) (by decide) (by decide) (by omega) (by omega) rt_S2 rt_S2'
      hinv hX
  have tB : Triv 3 1 (opsQ.eval (m + 4) (wc 4 (m + 4) (uBL ++ [r'] ++ uBR))) := by
    rw [wc_conj]
    have hX := triv_rot (m + 4) (by omega) hr'
    simp only [Bool.false_eq_true, if_false] at hX
    have hinv : opsQ.eval (m + 4) (wc 4 (m + 4) uBR) * opsQ.eval (m + 4) (wc 4 (m + 4) uBL) = 1 :=
      eval_inv (uRL m ih4)
    exact triv_conj (K := 4) (by omega) (fun x hx => (hu x (by simp [hx])).2.2.2)
      (fun x hx => (hu x (by simp [hx])).2.2.2) (by omega) (by omega) rt_uBL rt_uBR hinv hX
  have hsem := sep_sem (K := 4) (M := m + 4) (by decide : (0 : Fin 2) ≠ 1) tA tB
  -- the letters avoid wire `4`
  have mem : ∀ x ∈ ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]) ++ (uBL ++ [r'] ++ uBR),
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((rfl | rfl) | rfl) | ((hx | rfl) | hx)
    · exact (hu _ (by simp)).imp_right (fun h => ⟨h.1, h.2.1⟩)
    · exact ⟨hA.1, hA.2.1, hA.2.2.1⟩
    · exact (hu _ (by simp)).imp_right (fun h => ⟨h.1, h.2.1⟩)
    · exact (hu x (by simp [hx])).imp_right (fun h => ⟨h.1, h.2.1⟩)
    · exact ⟨hB.1, hB.2.1, hB.2.2.1⟩
    · exact (hu x (by simp [hx])).imp_right (fun h => ⟨h.1, h.2.1⟩)
  have mem' : ∀ x ∈ (uBL ++ [r'] ++ uBR) ++ ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]),
      x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := fun x hx =>
    mem x (by simp only [List.mem_append] at hx ⊢; tauto)
  have e1 : (([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]) ++ (uBL ++ [r'] ++ uBR)).map (Lt.drop 4) =
      ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]) ++ (uBL ++ [r'] ++ uBR) := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem x hx).2.2), List.map_id]
  have e2 : ((uBL ++ [r'] ++ uBR) ++ ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)])).map (Lt.drop 4) =
      (uBL ++ [r'] ++ uBR) ++ ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]) := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem' x hx).2.2), List.map_id]
  rw [← e1, ← e2] at hsem
  have hw : Derivable (theory (m + 5))
      (wc 5 (m + 5) (([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]) ++ (uBL ++ [r'] ++ uBR)))
      (wc 5 (m + 5) ((uBL ++ [r'] ++ uBR) ++ ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]))) :=
    SE.Frame.window (frame 4) m ih (q := 4) le_rfl
      (fun x hx => ⟨(mem x hx).1, (mem x hx).2.1⟩) (fun x hx => ⟨(mem' x hx).1, (mem' x hx).2.1⟩)
      hsem
  -- back to the gates
  have eA : wc 5 (m + 5) ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]) =
      swAt (m + 5) 2 * r.circ 4 (m + 5) * swAt (m + 5) 2 := by
    rw [wc_conj, wc_one', circS, rots_rebase hr]
  have eB : wc 5 (m + 5) (uBL ++ [r'] ++ uBR) = U m * r'.circ 4 (m + 5) * U' m := by
    rw [wc_conj, wcU, wcU', rots_rebase hr']
  unfold Comm
  rw [drawn_two, drawn_two]
  rw [wc_append 5 (m + 5) ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]) (uBL ++ [r'] ++ uBR),
    wc_append 5 (m + 5) (uBL ++ [r'] ++ uBR) ([Lt.s (L.S 2)] ++ [r] ++ [Lt.s (L.S 2)]), eA, eB] at hw
  exact hw

/-! ### The pairs and (339) -/

/-- Every piece of `A` commutes with every piece of `B`. -/
theorem pairs (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) :
    ∀ a ∈ ((pcs4 c₂ true c₁).map (cX 4 (m + 5) (xE c₁ c₂ x))).map
        (fun a => swAt (m + 5) 2 * a * swAt (m + 5) 2),
      ∀ b ∈ ((pcs4 c₃ false true).map (cX 4 (m + 5) (yB c₃ y))).map
        (fun a => U m * a * U' m), Comm (m + 5) a b := by
  intro a ha b hb
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha0
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb0
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']; exact commRR m ih hr hr'
  · rw [rots_cX hr, P3'_cX]; exact commRQ m ih (yB c₃ y) c₁ c₂ c₃ hr
  · rw [P3'_cX, rots_cX hr']; exact commBR m ih (xE c₁ c₂ x) c₂ c₃ hr'
  · rw [P3'_cX, P3'_cX]; exact commBQ m ih (xE c₁ c₂ x) (yB c₃ y) c₂ c₃

/-- (339) when the colourings are black, resp. white, on wire `3`. -/
theorem core339 (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) (hx : x 3 = true) (hy : y 3 = false) :
    Comm (m + 5) (mc (m + 5) .box [0] (cA (m + 5) x c₁ c₂))
      (mc (m + 5) .hg [1, 2] (cB (m + 5) y c₃)) :=
  Comm.congr (expA m ih x c₁ c₂ hx).symm (expB m ih y c₃ hy).symm
    (comm_drawn _ _ (pairs m ih x y c₁ c₂ c₃))

end Frame

/-! ## Back to the interface -/

/-- (339) from five wires on. -/
theorem comm339_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ c₃ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 5) (mc (m + 5) .box [0] (cA (m + 5) x c₁ c₂))
    (mc (m + 5) .hg [1, 2] (cB (m + 5) y c₃))) ?_ ?_
    (fun x y hx hy => core339 m ih x y c₁ c₂ c₃ hx hy) x y hxy
  · intro x y j hj hjN h
    have rA := swBH ih j hjN .box (Or.inl rfl) [0] [0] (cA (m + 5) (x ∘ Net.tau j) c₁ c₂)
      (cA (m + 5) x c₁ c₂) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau_of_lt (show 0 < j by omega)])
      (fun i hi => by
        simp only [cA, ctlOr, ctlAt_tau (show 2 < j by omega), ctlAt_tau (show 1 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN x hi])
    have rB := swBH ih j hjN .hg (Or.inr rfl) [1, 2] [1, 2] (cB (m + 5) (y ∘ Net.tau j) c₃)
      (cB (m + 5) y c₃) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp only [List.map_cons, List.map_nil, Net.tau_of_lt (show 1 < j by omega),
        Net.tau_of_lt (show 2 < j by omega)])
      (fun i hi => by
        simp only [cB, ctlOr, ctlAt_tau (show 0 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN y hi])
    exact Comm.congr rA rB (Comm.conj h (swsw _ j hjN))
  · intro x y h
    have hx := xAt_inv (m + 5) 3 (by omega)
    refine comm_flip h hx ?_ ?_
    · have e := eq81 (m + 5) .box [0] (cA (m + 5) (flipAt 3 x) c₁ c₂) 3 (flipAt 3 x 3)
        (by omega) (by decide) (by simp [cA, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 5) 3, mc (m + 5) .box [0] (cA (m + 5) (flipAt 3 x) c₁ c₂),
          xAt (m + 5) 3] = xAt (m + 5) 3 * mc (m + 5) .box [0] (cA (m + 5) (flipAt 3 x) c₁ c₂) *
          xAt (m + 5) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 5) (by omega) x i
      simp only [cA, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all
    · have e := eq81 (m + 5) .hg [1, 2] (cB (m + 5) (flipAt 3 y) c₃) 3 (flipAt 3 y 3)
        (by omega) (by decide) (by simp [cB, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 5) 3, mc (m + 5) .hg [1, 2] (cB (m + 5) (flipAt 3 y) c₃),
          xAt (m + 5) 3] = xAt (m + 5) 3 * mc (m + 5) .hg [1, 2] (cB (m + 5) (flipAt 3 y) c₃) *
          xAt (m + 5) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 5) (by omega) y i
      simp only [cB, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all

/-- (339) on five wires, in the form of the interface `D.eq339`. -/
theorem eq339_5 (ih : IH 5) (x y : ℕ → Bool) (hxy : DiffOn 3 5 x y) (c₁ c₂ c₃ : Bool) :
    Comm 5 (mc 5 .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 5 x))))
      (mc 5 .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 5 y))) :=
  comm339_ge5 5 le_rfl ih x y hxy c₁ c₂ c₃

end QCert.RealCliffordCH.Sec8.D.N13.L339
