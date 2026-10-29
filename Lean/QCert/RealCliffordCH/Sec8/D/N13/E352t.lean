/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (352) on three wires, given (348) on three wires

Two rotations, on the wires `0` and `1`, each controlled by the other's
target, with different colours on wire `2`.

* Both half-dots black: Lemma D.2's (139) and (140), with (81) on wire `2`
  and (317) for the sign of the first rotation.
* The first half-dot white: the decomposition of the second rotation with
  box wire `2` and hole `0` (`RotDec.dec_at`); its `H` gate `hg[0,1](2:y)`
  passes the first rotation by (348), its box `box[2](0:c₂, 1:●)` by (347)
  moved by the frame of the wires `2, 0, 1` (separated on wire `1`).
* The second half-dot white: the previous case under the swap of the wires
  `0, 1`.

(348) on three wires is a hypothesis (`H348`).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E351t

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.R347

open Circuit Net E Eng

/-- (348) at one width, as `N13.eq348` states it. -/
abbrev H348 (N : ℕ) : Prop := ∀ x y : ℕ → Bool, DiffOn 2 N x y → ∀ a c₁ : Bool,
  D.Comm N (mc N .hg [0, 1] (colOn 2 N x))
    (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N y)))

/-- (139) and (140). -/
theorem c139 (ih : IH 3) (b : Bool) :
    D.Comm 3 (mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 fun _ => true)))
      (mc 3 (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 true) (colOn 2 3 fun _ => false))) := by
  cases b
  · have h := d139 ih
    have el : l139 = drawn [mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 fun _ => true)),
        mc 3 .zx [1] (ctlOr (ctlAt 0 true) (colOn 2 3 fun _ => false))] := by
      set_option maxRecDepth 100000 in rfl
    have er : r139 = drawn [mc 3 .zx [1] (ctlOr (ctlAt 0 true) (colOn 2 3 fun _ => false)),
        mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 fun _ => true))] := by
      set_option maxRecDepth 100000 in rfl
    rw [el, er] at h
    exact h
  · have h := d140 ih
    have el : l140 = drawn [mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 fun _ => true)),
        mc 3 .xz [1] (ctlOr (ctlAt 0 true) (colOn 2 3 fun _ => false))] := by
      set_option maxRecDepth 100000 in rfl
    have er : r140 = drawn [mc 3 .xz [1] (ctlOr (ctlAt 0 true) (colOn 2 3 fun _ => false)),
        mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 fun _ => true))] := by
      set_option maxRecDepth 100000 in rfl
    rw [el, er] at h
    exact h

/-- The colours of a rotation on wire `0`, as `colOn 1`. -/
theorem ctl1 (c : Bool) (x : ℕ → Bool) : ∀ i < 3,
    ctlOr (ctlAt 1 c) (colOn 2 3 x) i = colOn 1 3 (fun j => if j = 1 then c else x j) i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ctlOr, ctlAt, colOn]

/-- The sign of the rotation on wire `0`, by (317). -/
theorem sign0 (h317 : H317 3) {B : Circ 3} (c : Bool) (x : ℕ → Bool)
    (h : D.Comm 3 (mc 3 .zx [0] (ctlOr (ctlAt 1 c) (colOn 2 3 x))) B) (a : Bool) :
    D.Comm 3 (mc 3 (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c) (colOn 2 3 x))) B := by
  have e : ∀ K, mc 3 K [0] (ctlOr (ctlAt 1 c) (colOn 2 3 x)) =
      mc 3 K [0] (colOn 1 3 (fun j => if j = 1 then c else x j)) :=
    fun K => Net.mc_congr _ _ _ (ctl1 c x)
  have hx := h317 (fun j => if j = 1 then c else x j)
  rw [N13.drawn_two, N13.drawn_two] at hx
  rw [e .zx] at h
  rw [e (Kind.sgnZX a)]
  cases a
  · exact h
  · exact N13.Comm.inv h hx.2 hx.1

/-- The swap of the wires `0, 1` moves a rotation from wire `0` to wire `1`
and back. -/
theorem sw01 (hsw : E.McSwapAll 3) (K : Kind) (hK : kindSp K = 1) (t t' : ℕ) (ht : Net.tau 0 t = t')
    (ht2 : t < 2) (c : Bool) (x : ℕ → Bool) :
    Derivable (theory 3) (swAt 3 0 * mc 3 K [t] (ctlOr (ctlAt (1 - t) c) (colOn 2 3 x)) * swAt 3 0)
      (mc 3 K [t'] (ctlOr (ctlAt (1 - t') c) (colOn 2 3 x))) := by
  have h := hsw 0 (by omega) K [t] (ctlOr (ctlAt (1 - t) c) (colOn 2 3 x)) (by simp [hK])
    (by simp) (by intro u hu; simp at hu; omega)
  rw [show drawn [swAt 3 0, mc 3 K [t] (ctlOr (ctlAt (1 - t) c) (colOn 2 3 x)), swAt 3 0] =
    swAt 3 0 * mc 3 K [t] (ctlOr (ctlAt (1 - t) c) (colOn 2 3 x)) * swAt 3 0 by
      simp [drawn, mul_assoc]] at h
  refine h.trans (der_of_eq ?_)
  rw [show [t].map (Net.tau 0) = [t'] by simp [ht]]
  refine Net.mc_congr _ _ _ (fun i hi => ?_)
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> (subst ht) <;>
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    simp [ctlOr, ctlAt, colOn, Net.tau, Function.comp]

/-- The first half-dot white. -/
theorem c352A (ih : IH 3) (hsw : E.McSwapAll 3) (h333 : H333 3) (h334 : H334 3)
    (h336 : H336 3) (h337 : H337 3) (h348 : H348 3) (x y : ℕ → Bool) (hxy : x 2 ≠ y 2)
    (a b c₂ : Bool) :
    D.Comm 3 (mc 3 (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 false) (colOn 2 3 x)))
      (mc 3 (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 3 y))) := by
  have hc : ∀ i < 3, ctlOr (ctlAt 0 c₂) (colOn 2 3 y) i = none ↔ i = 1 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ctlOr, ctlAt, colOn]
  have hd := dec_at le_rfl ih hsw h333 h334 b (t := 1) (b := 2) (h := 0) (by omega) (by omega)
    (by omega) (by decide) (by decide) (by decide) _ hc
  refine Comm.congr (Derivable.refl _) hd.symm (comm_dw b ?_ ?_)
  · -- (348)
    have e : mc 3 .hg [0, 1] (setCtl (ctlOr (ctlAt 0 c₂) (colOn 2 3 y)) 0 none) =
        mc 3 .hg [0, 1] (colOn 2 3 y) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
          simp [setCtl, ctlOr, ctlAt, colOn])
    rw [e]
    exact Derivable.symm (h348 y x ⟨2, le_rfl, by omega, Ne.symm hxy⟩ a false)
  · -- (347) on the wires `2, 0, 1`
    have hnd : [2, 0, 1].Nodup := by decide
    have hps : ∀ p ∈ [2, 0, 1], p < 3 := by decide
    have f0 : frm [2, 0, 1] 0 = 2 := frm_getD hnd hps (by simp)
    have f1 : frm [2, 0, 1] 1 = 0 := frm_getD hnd hps (by simp)
    have f2 : frm [2, 0, 1] 2 = 1 := frm_getD hnd hps (by simp)
    have h := comm347 le_rfl ih hsw h333 h334 h336 h337 (fun _ => true) (fun _ => false)
      ⟨2, le_rfl, by omega, by decide⟩ a c₂ (x 2)
    refine Derivable.symm (comm_frame (hsw.toK (fun _ => True)) hnd hps trivial trivial rfl
      (by simp) (by intro t ht; simp at ht; omega) (by simp [f0]) (by rw [kindSp_sgn]; rfl)
      (by simp) (by intro t ht; simp at ht; omega) (by simp [f1]) ?_ ?_ h)
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp [f0, setCtl, ctlOr, ctlAt, colOn]
      · simp [f1, setCtl, ctlOr, ctlAt, colOn]
      · simp [f2, setCtl, ctlOr, ctlAt, colOn]
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp [f0, ctlOr, ctlAt, colOn]
      · simp [f1, ctlOr, ctlAt, colOn]
      · simp [f2, ctlOr, ctlAt, colOn]

/-- (352) on three wires, given (348) on three wires. -/
theorem comm352_3 (ih : IH 3) (hsw : E.McSwapAll 3) (h333 : H333 3) (h334 : H334 3)
    (h317 : H317 3) (h336 : H336 3) (h337 : H337 3) (h348 : H348 3) (x y : ℕ → Bool)
    (hxy : DiffOn 2 3 x y) (a b c₁ c₂ : Bool) :
    D.Comm 3 (mc 3 (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 x)))
      (mc 3 (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 3 y))) := by
  obtain ⟨j, hj2, hj3, hxyj⟩ := hxy
  have h2 : x 2 ≠ y 2 := by
    have : j = 2 := by omega
    subst this; exact hxyj
  cases c₁
  · exact c352A ih hsw h333 h334 h336 h337 h348 x y h2 a b c₂
  cases c₂
  · -- the second half-dot white: the previous case under the swap of the wires `0, 1`
    have k := c352A ih hsw h333 h334 h336 h337 h348 y x (Ne.symm h2) b a true
    have hs := swsw 3 0 (by omega)
    have ea := sw01 hsw (Kind.sgnZX a) (kindSp_sgn a) 1 0 (by simp [Net.tau]) (by omega) true x
    have eb := sw01 hsw (Kind.sgnZX b) (kindSp_sgn b) 0 1 (by simp [Net.tau]) (by omega) false y
    exact Derivable.symm (Comm.congr eb ea (Comm.conj k hs))
  -- both half-dots black: (139), (140), with (81) on wire `2`
  refine sign0 h317 true x ?_ a
  have base : ∀ x y : ℕ → Bool, x 2 = true → y 2 = false →
      D.Comm 3 (mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 x)))
        (mc 3 (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 true) (colOn 2 3 y))) := by
    intro x y hx hy
    have ex : mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 x)) =
        mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 fun _ => true)) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
          simp [ctlOr, ctlAt, colOn, hx])
    have ey : mc 3 (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 true) (colOn 2 3 y)) =
        mc 3 (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 true) (colOn 2 3 fun _ => false)) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
          simp [ctlOr, ctlAt, colOn, hy])
    rw [ex, ey]; exact c139 ih b
  cases hx : x 2
  · -- `X` on wire `2`
    have hy : y 2 = true := by cases hy : y 2 <;> simp_all
    have flA : ∀ z : ℕ → Bool, Derivable (theory 3)
        (xAt 3 2 * mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 z)) * xAt 3 2)
        (mc 3 .zx [0] (ctlOr (ctlAt 1 true) (colOn 2 3 (MergeAll.flip1 z 2)))) := by
      intro z
      refine (x81 .zx [0] _ 2 (z 2) (by omega) (by simp) (by simp [ctlOr, ctlAt, colOn])).trans
        (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simp [setCtl, ctlOr, ctlAt, colOn, MergeAll.flip1]
    have flB : ∀ z : ℕ → Bool, Derivable (theory 3)
        (xAt 3 2 * mc 3 (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 true) (colOn 2 3 z)) * xAt 3 2)
        (mc 3 (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 true) (colOn 2 3 (MergeAll.flip1 z 2)))) := by
      intro z
      refine (x81 (Kind.sgnZX b) [1] _ 2 (z 2) (by omega) (by simp) (by simp [ctlOr, ctlAt, colOn])).trans
        (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simp [setCtl, ctlOr, ctlAt, colOn, MergeAll.flip1]
    have k := base (MergeAll.flip1 x 2) (MergeAll.flip1 y 2) (by simp [MergeAll.flip1, hx])
      (by simp [MergeAll.flip1, hy])
    have e2 : ∀ z : ℕ → Bool, MergeAll.flip1 (MergeAll.flip1 z 2) 2 = z := fun z => by
      funext i; simp only [MergeAll.flip1]; split_ifs <;> simp
    have k2 := comm_flip k (D.xAt_inv 3 2 (by omega)) (flA (MergeAll.flip1 x 2))
      (flB (MergeAll.flip1 y 2))
    rwa [e2, e2] at k2
  · have hy : y 2 = false := by cases hy : y 2 <;> simp_all
    exact base x y hx hy

end QCert.RealCliffordCH.Sec8.D.N13.R347
