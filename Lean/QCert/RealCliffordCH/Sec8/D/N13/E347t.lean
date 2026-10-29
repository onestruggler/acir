/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (349) on three wires, through (341)

On three wires the paper's decomposition argument (page 234) has no wire to
spare.  For (349) the decomposition with box wire `0` and hole `2`
(`RotDec.dec_at`) still works: the box against the `H` gate is (337), and
the `H` gate of the rotation, `hg[2,1](0:c₁)`, against `hg[0,1](2:x)` is
(341) on three wires (two multi-controlled `H` gates on the same `H` wire,
the hole of each the control of the other), which is Lemma D.2's (135)
(`d135`, `CH(2→0)` and `CH(1→0)` commute) under the swap of the wires `0, 1`,
coloured by `X` on the wires `0` and `2` ((81), and (316) for the holes).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E347

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.R347

open Circuit Net E Eng

/-- (135): `CH(2→0)` and `CH(1→0)`, as multi-controlled `H` gates. -/
theorem c135 (ih : IH 3) :
    D.Comm 3 (mc 3 .hg [1, 0] (ctlAt 2 true)) (mc 3 .hg [2, 0] (ctlAt 1 true)) := by
  have h := d135 ih
  have eA : mc 3 .hg [1, 0] (ctlAt 2 true) = circW 3 [L.S 0, L.K 1, L.S 0] := by
    set_option maxRecDepth 100000 in rfl
  have eK : (ch : Circ 3) = circW 3 [L.K 0] := by
    set_option maxRecDepth 100000 in rfl
  have el : l135 = drawn [circW 3 [L.S 0, L.K 1, L.S 0], circW 3 [L.K 0]] := by
    set_option maxRecDepth 100000 in rfl
  have er : r135 = drawn [circW 3 [L.K 0], circW 3 [L.S 0, L.K 1, L.S 0]] := by
    set_option maxRecDepth 100000 in rfl
  rw [el, er] at h
  have hB := N13.hg_ch3
  rw [eK] at hB
  rw [eA]
  exact Comm.congr (Derivable.refl _) hB.symm h

/-- (316) for `hg[2,1]` on three wires: `X` on its hole passes it. -/
theorem x2_hg21 (ih : IH 3) (c : Bool) :
    Derivable (theory 3) (xAt 3 2 * mc 3 .hg [2, 1] (ctlAt 0 c) * xAt 3 2)
      (mc 3 .hg [2, 1] (ctlAt 0 c)) := by
  have hs := swsw 3 0 (by omega)
  have hx : Derivable (theory 3) (swAt 3 0 * xAt 3 2 * swAt 3 0) (xAt 3 2) := by
    have := x_conj 3 0 2 (by omega)
    rwa [show Net.tau 0 2 = 2 by simp [Net.tau]] at this
  have ha := swBH ih 0 (by omega) .hg (Or.inr rfl) [2, 0] [2, 1] (ctlAt 1 c) (ctlAt 0 c) rfl
    (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ctlAt, Net.tau])
  have h0 := x2_hg 3 le_rfl ih c (fun _ => true)
  have e : mc 3 .hg [2, 0] (ctlOr (ctlAt 1 c) (colOn 3 3 fun _ => true)) =
      mc 3 .hg [2, 0] (ctlAt 1 c) :=
    Net.mc_congr _ _ _ (fun i hi => by simp only [ctlOr, colOn]; rw [if_neg (by omega), Option.or_none])
  rw [e] at h0
  exact fix_conj hs hx ha h0

/-- (81) on a control, as a conjugation. -/
theorem x81 {N : ℕ} (K : Kind) (tg : List ℕ) (e : ℕ → Option Bool) (j : ℕ) (b : Bool)
    (hjN : j < N) (hjt : j ∉ tg) (hej : e j = some b) :
    Derivable (theory N) (xAt N j * mc N K tg e * xAt N j) (mc N K tg (setCtl e j (some !b))) := by
  have h := D.eq81 N K tg e j b hjN hjt hej
  rwa [show drawn [xAt N j, mc N K tg e, xAt N j] = xAt N j * mc N K tg e * xAt N j by
    simp [drawn, mul_assoc]] at h

/-- (341) on three wires, every colour. -/
theorem c341 (ih : IH 3) (u v : Bool) :
    D.Comm 3 (mc 3 .hg [0, 1] (ctlAt 2 u)) (mc 3 .hg [2, 1] (ctlAt 0 v)) := by
  have hs := swsw 3 0 (by omega)
  -- black: (135) under the swap of the wires `0, 1`
  have base : D.Comm 3 (mc 3 .hg [0, 1] (ctlAt 2 true)) (mc 3 .hg [2, 1] (ctlAt 0 true)) := by
    have a := swBH ih 0 (by omega) .hg (Or.inr rfl) [1, 0] [0, 1] (ctlAt 2 true) (ctlAt 2 true) rfl
      (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ctlAt, Net.tau])
    have b := swBH ih 0 (by omega) .hg (Or.inr rfl) [2, 0] [2, 1] (ctlAt 1 true) (ctlAt 0 true) rfl
      (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ctlAt, Net.tau])
    exact Comm.congr a b (Comm.conj (c135 ih) hs)
  -- `X` on wire `2`: flips the first, passes the hole of the second
  have flip2 : ∀ u v, D.Comm 3 (mc 3 .hg [0, 1] (ctlAt 2 u)) (mc 3 .hg [2, 1] (ctlAt 0 v)) →
      D.Comm 3 (mc 3 .hg [0, 1] (ctlAt 2 (!u))) (mc 3 .hg [2, 1] (ctlAt 0 v)) := by
    intro u v h
    refine comm_flip h (D.xAt_inv 3 2 (by omega)) ((x81 .hg [0, 1] _ 2 u (by omega) (by decide)
      (by simp [ctlAt])).trans (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))) (x2_hg21 ih v)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [setCtl, ctlAt]
  -- `X` on wire `0`: passes the hole of the first, flips the second
  have flip0 : ∀ u v, D.Comm 3 (mc 3 .hg [0, 1] (ctlAt 2 u)) (mc 3 .hg [2, 1] (ctlAt 0 v)) →
      D.Comm 3 (mc 3 .hg [0, 1] (ctlAt 2 u)) (mc 3 .hg [2, 1] (ctlAt 0 (!v))) := by
    intro u v h
    have e : mc 3 .hg [0, 1] (colOn 2 3 fun _ => u) = mc 3 .hg [0, 1] (ctlAt 2 u) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [colOn, ctlAt])
    have h0 := x0_hole_hg 3 le_rfl ih (fun _ => u)
    rw [e] at h0
    refine comm_flip h (D.xAt_inv 3 0 (by omega)) h0 ((x81 .hg [2, 1] _ 0 v (by omega) (by decide)
      (by simp [ctlAt])).trans (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_))))
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [setCtl, ctlAt]
  cases u <;> cases v
  · exact flip0 false true (flip2 true true base)
  · exact flip2 true true base
  · exact flip0 true true base
  · exact base

/-- (349) on three wires. -/
theorem comm349_3 (ih : IH 3) (hsw : E.McSwapAll 3) (h333 : H333 3) (h334 : H334 3)
    (h337 : H337 3) (x y : ℕ → Bool) (hxy : DiffOn 2 3 x y) (a c₁ : Bool) :
    D.Comm 3 (mc 3 .hg [0, 1] (colOn 2 3 x))
      (mc 3 (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₁) (colOn 2 3 y))) := by
  have hc : ∀ i < 3, ctlOr (ctlAt 0 c₁) (colOn 2 3 y) i = none ↔ i = 1 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ctlOr, ctlAt, colOn]
  have hd := dec_at le_rfl ih hsw h333 h334 a (t := 1) (b := 0) (h := 2) (by omega) (by omega)
    (by omega) (by decide) (by decide) (by decide) _ hc
  refine Comm.congr (Derivable.refl _) hd.symm (comm_dw a ?_ ?_)
  · -- (341)
    have e1 : mc 3 .hg [0, 1] (colOn 2 3 x) = mc 3 .hg [0, 1] (ctlAt 2 (x 2)) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [colOn, ctlAt])
    have e2 : mc 3 .hg [2, 1] (setCtl (ctlOr (ctlAt 0 c₁) (colOn 2 3 y)) 2 none) =
        mc 3 .hg [2, 1] (ctlAt 0 c₁) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
          simp [setCtl, ctlOr, ctlAt, colOn])
    rw [e1, e2]; exact c341 ih (x 2) c₁
  · -- (337)
    have e : mc 3 .box [0] (setCtl (setCtl (ctlOr (ctlAt 0 c₁) (colOn 2 3 y)) 0 none) 1 (some true)) =
        mc 3 .box [0] (ctlOr (ctlAt 1 true) (colOn 2 3 y)) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
          simp [setCtl, ctlOr, ctlAt, colOn])
    rw [e]
    obtain ⟨j, hj2, hjN, hxyj⟩ := hxy
    exact Derivable.symm (h337 y x ⟨j, hj2, hjN, Ne.symm hxyj⟩ true)

end QCert.RealCliffordCH.Sec8.D.N13.R347
