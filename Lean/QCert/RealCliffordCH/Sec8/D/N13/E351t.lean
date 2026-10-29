/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (351) on three wires

Two rotations on wire `0`, controlled by the wires `1, 2` with different
colourings.  Not by the paper's argument, which has no wire to spare here:

* the colourings differ on wire `2` only: Lemma D.2's (136) and (137) say
  that both products are the rotation controlled by wire `1` alone, so the
  two commute; (81) on both gates moves the colours, (317) the signs;
* on wire `1` only: the same under the swap of the wires `1, 2` (rotations
  move with (353), `E.McSwapAll`);
* on both wires: the decomposition of the second rotation with box wire `1`
  and hole `2` (`RotDec.dec_at`); the first passes the box by (347) and the
  `H` gate by (349) on three wires (`E347t.comm349_3`), both moved by a frame.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E347t

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.R347

open Circuit Net E Eng

/-- The colours `u`, `v` of the wires `1`, `2`. -/
def cw (u v : Bool) : ℕ → Bool := fun i => if i = 1 then u else v

theorem colOn_cw (x : ℕ → Bool) : ∀ i < 3, colOn 1 3 x i = colOn 1 3 (cw (x 1) (x 2)) i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [colOn, cw]

/-- The signs, by (317) (Lemma B.5). -/
theorem comm_signs (h317 : H317 3) {x y : ℕ → Bool}
    (h : D.Comm 3 (mc 3 .zx [0] (colOn 1 3 x)) (mc 3 .zx [0] (colOn 1 3 y))) (a b : Bool) :
    D.Comm 3 (mc 3 (Kind.sgnZX a) [0] (colOn 1 3 x)) (mc 3 (Kind.sgnZX b) [0] (colOn 1 3 y)) := by
  have hx := h317 x
  have hy := h317 y
  rw [N13.drawn_two, N13.drawn_two] at hx hy
  have left : ∀ {B : Circ 3}, D.Comm 3 (mc 3 .zx [0] (colOn 1 3 x)) B →
      D.Comm 3 (mc 3 .xz [0] (colOn 1 3 x)) B := fun hB => N13.Comm.inv hB hx.2 hx.1
  have right : ∀ {A : Circ 3}, D.Comm 3 A (mc 3 .zx [0] (colOn 1 3 y)) →
      D.Comm 3 A (mc 3 .xz [0] (colOn 1 3 y)) := fun hA =>
    Derivable.symm (N13.Comm.inv (Derivable.symm hA) hy.2 hy.1)
  cases a <;> cases b
  · exact h
  · exact right h
  · exact left h
  · exact right (left h)

/-- (81) on a control of a rotation on wire `0`. -/
theorem flipR3 (a : Bool) {j : ℕ} (hj : 1 ≤ j) (hj3 : j < 3) (x : ℕ → Bool) :
    Derivable (theory 3) (xAt 3 j * mc 3 (Kind.sgnZX a) [0] (colOn 1 3 x) * xAt 3 j)
      (mc 3 (Kind.sgnZX a) [0] (colOn 1 3 (MergeAll.flip1 x j))) :=
  (x81 _ [0] _ j (x j) hj3 (by simp; omega) (by simp [colOn, hj, hj3])).trans
    (der_of_eq (Net.mc_congr _ _ _ (ctl_flipR x hj hj3)))

/-- (136), (137): the colourings `(●, ○)` and `(●, ●)`. -/
theorem c136 (ih : IH 3) :
    D.Comm 3 (mc 3 .zx [0] (colOn 1 3 (cw true false))) (mc 3 .zx [0] (colOn 1 3 (cw true true))) := by
  have h6 := d136 ih
  have h7 := d137 ih
  have e6 : l136 = drawn [mc 3 .zx [0] (colOn 1 3 (cw true false)),
      mc 3 .zx [0] (colOn 1 3 (cw true true))] := by
    set_option maxRecDepth 100000 in rfl
  have e7 : l137 = drawn [mc 3 .zx [0] (colOn 1 3 (cw true true)),
      mc 3 .zx [0] (colOn 1 3 (cw true false))] := by
    set_option maxRecDepth 100000 in rfl
  have e67 : r136 = r137 := rfl
  rw [e6] at h6
  rw [e7, ← e67] at h7
  exact h6.trans h7.symm

theorem fl1 (u v : Bool) : ∀ i < 3,
    colOn 1 3 (MergeAll.flip1 (cw u v) 1) i = colOn 1 3 (cw (!u) v) i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [colOn, MergeAll.flip1, cw]

theorem fl2 (u v : Bool) : ∀ i < 3,
    colOn 1 3 (MergeAll.flip1 (cw u v) 2) i = colOn 1 3 (cw u (!v)) i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [colOn, MergeAll.flip1, cw]

/-- (81) on the wire `j` of both rotations. -/
theorem flipC {j : ℕ} (hj : 1 ≤ j) (hj3 : j < 3) {x y x₁ y₁ : ℕ → Bool}
    (ex : ∀ i < 3, colOn 1 3 (MergeAll.flip1 x j) i = colOn 1 3 x₁ i)
    (ey : ∀ i < 3, colOn 1 3 (MergeAll.flip1 y j) i = colOn 1 3 y₁ i)
    (h : D.Comm 3 (mc 3 .zx [0] (colOn 1 3 x)) (mc 3 .zx [0] (colOn 1 3 y))) :
    D.Comm 3 (mc 3 .zx [0] (colOn 1 3 x₁)) (mc 3 .zx [0] (colOn 1 3 y₁)) :=
  comm_flip h (D.xAt_inv 3 j hj3)
    ((flipR3 false hj hj3 x).trans (der_of_eq (Net.mc_congr _ _ _ ex)))
    ((flipR3 false hj hj3 y).trans (der_of_eq (Net.mc_congr _ _ _ ey)))

/-- Colourings differing on wire `2` only. -/
theorem c351w2 (ih : IH 3) (u v : Bool) :
    D.Comm 3 (mc 3 .zx [0] (colOn 1 3 (cw u v))) (mc 3 .zx [0] (colOn 1 3 (cw u (!v)))) := by
  have tf := c136 ih
  have tt : D.Comm 3 (mc 3 .zx [0] (colOn 1 3 (cw true true)))
      (mc 3 .zx [0] (colOn 1 3 (cw true false))) :=
    flipC (j := 2) (by omega) (by omega) (fl2 true false) (fl2 true true) tf
  have ff : D.Comm 3 (mc 3 .zx [0] (colOn 1 3 (cw false false)))
      (mc 3 .zx [0] (colOn 1 3 (cw false true))) :=
    flipC (j := 1) (by omega) (by omega) (fl1 true false) (fl1 true true) tf
  have ft : D.Comm 3 (mc 3 .zx [0] (colOn 1 3 (cw false true)))
      (mc 3 .zx [0] (colOn 1 3 (cw false false))) :=
    flipC (j := 1) (by omega) (by omega) (fl1 true true) (fl1 true false) tt
  cases u <;> cases v
  · exact ff
  · exact ft
  · exact tf
  · exact tt

/-- (347) on three wires: the box on wire `1` (black on `0`) and a rotation on
wire `0`, by the frame of the wires `1, 0`. -/
theorem c347f (ih : IH 3) (hsw : E.McSwapAll 3) (h333 : H333 3) (h334 : H334 3)
    (h336 : H336 3) (h337 : H337 3) (x y : ℕ → Bool) (h2 : y 2 ≠ x 2) (a : Bool) :
    D.Comm 3 (mc 3 .box [1] (setCtl (setCtl (colOn 1 3 y) 1 none) 0 (some true)))
      (mc 3 (Kind.sgnZX a) [0] (colOn 1 3 x)) := by
  have hnd : [1, 0].Nodup := by decide
  have hps : ∀ p ∈ [1, 0], p < 3 := by decide
  have f0 : frm [1, 0] 0 = 1 := frm_getD hnd hps (by simp)
  have f1 : frm [1, 0] 1 = 0 := frm_getD hnd hps (by simp)
  have f2 : frm [1, 0] 2 = 2 := by
    obtain ⟨hm, hl⟩ := frm_out' hnd hps (j := 2) (by simp) (by omega)
    simp at hm; omega
  have h := comm347 le_rfl ih hsw h333 h334 h336 h337 (fun _ => y 2) (fun _ => x 2)
    ⟨2, le_rfl, by omega, h2⟩ a true (x 1)
  refine comm_frame (hsw.toK (fun _ => True)) hnd hps trivial trivial rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0]) (by rw [kindSp_sgn]; rfl) (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f1]) ?_ ?_ h
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

/-- (349) on three wires: the `H` gate on wire `0` with its hole on `2` and a
rotation on wire `0`, by the frame of the wires `2, 0, 1`. -/
theorem c349f (ih : IH 3) (hsw : E.McSwapAll 3) (h333 : H333 3) (h334 : H334 3)
    (h337 : H337 3) (x y : ℕ → Bool) (h1 : y 1 ≠ x 1) (a : Bool) :
    D.Comm 3 (mc 3 .hg [2, 0] (setCtl (colOn 1 3 y) 2 none))
      (mc 3 (Kind.sgnZX a) [0] (colOn 1 3 x)) := by
  have hnd : [2, 0, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 0, 1], p < 3 := by decide
  have f0 : frm [2, 0, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 0, 1] 1 = 0 := frm_getD hnd hps (by simp)
  have f2 : frm [2, 0, 1] 2 = 1 := frm_getD hnd hps (by simp)
  have h := comm349_3 ih hsw h333 h334 h337 (fun _ => y 1) (fun _ => x 1)
    ⟨2, le_rfl, by omega, h1⟩ a (x 2)
  refine comm_frame (hsw.toK (fun _ => True)) hnd hps trivial trivial rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f1]) (by rw [kindSp_sgn]; rfl) (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f1]) ?_ ?_ h
  · intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simp [f0, setCtl, colOn]
    · simp [f1, setCtl, colOn]
    · simp [f2, setCtl, colOn]
  · intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simp [f0, ctlOr, ctlAt, colOn]
    · simp [f1, ctlOr, ctlAt, colOn]
    · simp [f2, ctlOr, ctlAt, colOn]

/-- Colourings differing on wire `2` only, any colourings and signs. -/
theorem c351only2 (ih : IH 3) (h317 : H317 3) (x y : ℕ → Bool) (h1 : x 1 = y 1)
    (h2 : x 2 ≠ y 2) (a b : Bool) :
    D.Comm 3 (mc 3 (Kind.sgnZX a) [0] (colOn 1 3 x)) (mc 3 (Kind.sgnZX b) [0] (colOn 1 3 y)) := by
  have hy2 : y 2 = !x 2 := by
    cases hx : x 2 <;> cases hy : y 2 <;> simp_all
  have ex : mc 3 .zx [0] (colOn 1 3 (cw (x 1) (x 2))) = mc 3 .zx [0] (colOn 1 3 x) :=
    (Net.mc_congr _ _ _ (colOn_cw x)).symm
  have ey : mc 3 .zx [0] (colOn 1 3 (cw (x 1) (!x 2))) = mc 3 .zx [0] (colOn 1 3 y) := by
    rw [h1, ← hy2]; exact (Net.mc_congr _ _ _ (colOn_cw y)).symm
  have h := c351w2 ih (x 1) (x 2)
  rw [ex, ey] at h
  exact comm_signs h317 h a b

/-- (351) on three wires, different colourings. -/
theorem comm351_3 (ih : IH 3) (hsw : E.McSwapAll 3) (h333 : H333 3) (h334 : H334 3)
    (h317 : H317 3) (h336 : H336 3) (h337 : H337 3) (x y : ℕ → Bool) (hd : DiffOn 1 3 x y)
    (a b : Bool) :
    D.Comm 3 (mc 3 (Kind.sgnZX a) [0] (colOn 1 3 x)) (mc 3 (Kind.sgnZX b) [0] (colOn 1 3 y)) := by
  obtain ⟨j, hj1, hj3, hxyj⟩ := hd
  by_cases h1 : x 1 = y 1
  · have h2 : x 2 ≠ y 2 := by
      rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
      · exact absurd h1 hxyj
      · exact hxyj
    exact c351only2 ih h317 x y h1 h2 a b
  by_cases h2 : x 2 = y 2
  · -- the swap of the wires `1, 2`
    have hs := swsw 3 1 (by omega)
    have sw : ∀ (c : Bool) (z : ℕ → Bool), Derivable (theory 3)
        (swAt 3 1 * mc 3 (Kind.sgnZX c) [0] (colOn 1 3 (cw (z 2) (z 1))) * swAt 3 1)
        (mc 3 (Kind.sgnZX c) [0] (colOn 1 3 z)) := by
      intro c z
      have h := hsw 1 (by omega) (Kind.sgnZX c) [0] (colOn 1 3 (cw (z 2) (z 1)))
        (by rw [kindSp_sgn]; rfl) (by simp) (by intro t ht; simp at ht; omega)
      rw [show drawn [swAt 3 1, mc 3 (Kind.sgnZX c) [0] (colOn 1 3 (cw (z 2) (z 1))), swAt 3 1] =
        swAt 3 1 * mc 3 (Kind.sgnZX c) [0] (colOn 1 3 (cw (z 2) (z 1))) * swAt 3 1 by
          simp [drawn, mul_assoc]] at h
      refine h.trans (der_of_eq ?_)
      rw [show ([0] : List ℕ).map (Net.tau 1) = [0] by simp [Net.tau]]
      refine Net.mc_congr _ _ _ (fun i hi => ?_)
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simp [colOn, cw, Net.tau, Function.comp]
    have k := c351only2 ih h317 (cw (x 2) (x 1)) (cw (y 2) (y 1)) (by simp [cw, h2])
      (by simpa [cw] using h1) a b
    exact Comm.congr (sw a x) (sw b y) (Comm.conj k hs)
  · -- the colourings differ on both wires
    have hc : ∀ i < 3, colOn 1 3 y i = none ↔ i = 0 := by
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [colOn]
    have hdc := dec_at le_rfl ih hsw h333 h334 b (t := 0) (b := 1) (h := 2) (by omega) (by omega)
      (by omega) (by decide) (by decide) (by decide) _ hc
    refine Comm.congr (Derivable.refl _) hdc.symm (comm_dw b ?_ ?_)
    · exact Derivable.symm (c349f ih hsw h333 h334 h337 x y (Ne.symm h1) a)
    · exact Derivable.symm (c347f ih hsw h333 h334 h336 h337 x y (Ne.symm h2) a)

end QCert.RealCliffordCH.Sec8.D.N13.R347
