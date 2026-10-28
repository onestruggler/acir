/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (359): `XZ`, `ZX` on a control exchange its colour

The paper's proof.  `XZ = X · Z` and `ZX = Z · X` on the control wire `w`; `X`
there on both sides exchanges the colour ((81)), and `Z` there passes the gate:
`Z` on wire `w` is the box on wire `0` controlled by wire `w` (`zw_box`), which
by (309) over every colouring of the other wires is a product of boxes with
every control, each passing the gate by (346) (`comm_zw`).
-/
import QCert.RealCliffordCH.Sec8.D.N15.E356b

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-- The single-qubit `ZX` gate (`X`, then `Z`) on wire `j` (as in `D/N15.lean`). -/
def zxAt (N j : ℕ) : Circ N := placeG N (zx 0) [j]

/-- The single-qubit `XZ` gate (`Z`, then `X`) on wire `j` (as in `D/N15.lean`). -/
def xzAt (N j : ℕ) : Circ N := placeG N (xz 0) [j]

section Place

variable {N : ℕ}

theorem placeG_mul1 (w : ℕ) (hw : w < N) (a b : Circ 1) :
    Derivable (theory N) (placeG N (a * b) [w]) (placeG N a [w] * placeG N b [w]) := by
  rw [placeG_eq, placeG_eq, placeG_eq, atBot_mul]
  exact Net.placedBy_mul _ (netK_spec (ps := [w]) (by simp) (by simpa using hw) 1 le_rfl).1 _ _

theorem placeG_der1 (w : ℕ) (hw : w < N) (hN : 1 ≤ N) {a b : Circ 1}
    (h : Derivable (theory 1) a b) : Derivable (theory N) (placeG N a [w]) (placeG N b [w]) := by
  rw [placeG_eq, placeG_eq]
  exact placedBy_cong _ (der_atBot h N hN)

theorem placeG_one1 (w : ℕ) (hw : w < N) : Derivable (theory N) (placeG N (1 : Circ 1) [w]) 1 := by
  rw [placeG_eq]
  have e : atBot N (1 : Circ 1) = 1 := by
    have := atBot_drawn N ([] : List (Circ 1)); simpa [drawn] using this
  rw [e]
  exact Net.placedBy_one _ (netK_spec (ps := [w]) (by simp) (by simpa using hw) 1 le_rfl).1

/-- `Z` on wire `w` is an involution. -/
theorem zw_inv (w : ℕ) (hw : w < N) :
    Derivable (theory N) (placeG N (z : Circ 1) [w] * placeG N (z : Circ 1) [w]) 1 := by
  have h := N8.rule_full Rule.e2
  rw [drawn_two'] at h
  have h1 := placeG_der1 w hw (by omega) h
  have e : (drawn ([] : List (Circ 1))) = 1 := rfl
  rw [e] at h1
  exact (placeG_mul1 w hw z z).symm.trans (h1.trans (placeG_one1 w hw))

end Place

section Ctl

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- `Z` on wire `1` is the box on wire `0` controlled by wire `1`. -/
theorem z1_box :
    Derivable (theory (M + 3)) (placeG (M + 3) (z : Circ 1) [1]) (mc (M + 3) .box [0] (ctlAt 1 true)) := by
  have hS := swsw (M + 3) 0 (by omega)
  have h := z0_box ih
  have hz : Derivable (theory (M + 3)) (swAt (M + 3) 0 * Z0 M * swAt (M + 3) 0)
      (placeG (M + 3) (z : Circ 1) [1]) := by
    have := placeG_swap (N := M + 3) (z : Circ 1) (ps := [0]) (by simp) (by simp) rfl 0 (by omega)
    rw [conj3, show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau],
      placeG_single _ _ (by omega)] at this
    exact this
  refine hz.symm.trans ?_
  -- `S (S B S) S = B`
  have k := dright (swAt (M + 3) 0) (dleft (swAt (M + 3) 0) h.symm)
  refine k.trans ?_
  have e : swAt (M + 3) 0 * (swAt (M + 3) 0 * mc (M + 3) .box [0] (ctlAt 1 true) * swAt (M + 3) 0) *
      swAt (M + 3) 0 = (swAt (M + 3) 0 * swAt (M + 3) 0) * mc (M + 3) .box [0] (ctlAt 1 true) *
        (swAt (M + 3) 0 * swAt (M + 3) 0) := by simp only [mul_assoc]
  rw [e]
  have := dmul (dright (mc (M + 3) .box [0] (ctlAt 1 true)) hS) hS
  simpa using this

/-- `Z` on wire `w` is the box on wire `0` controlled by wire `w`. -/
theorem zw_box (w : ℕ) (hw1 : 1 ≤ w) (hwN : w < M + 3) :
    Derivable (theory (M + 3)) (placeG (M + 3) (z : Circ 1) [w]) (mc (M + 3) .box [0] (ctlAt w true)) := by
  have hnd : [0, w].Nodup := by simp; omega
  have hps : ∀ p ∈ [0, w], p < M + 3 := by simp; omega
  have f0 : frm [0, w] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, w] 1 = w := frm_getD hnd hps (by simp)
  have hk : ∀ j, 2 ≤ j → j < M + 3 → frm [0, w] j ≠ 0 ∧ frm [0, w] j ≠ w := by
    intro j hj hjN
    have := (frm_out' hnd hps (j := j) (by simp; omega) hjN).1
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at this
    exact this
  have fz : Derivable (theory (M + 3)) (placedBy (M + 3) (netOf [0, w]) (placeG (M + 3) (z : Circ 1) [1]))
      (placeG (M + 3) (z : Circ 1) [w]) := by
    have := placeG_net (N := M + 3) (z : Circ 1) (ps := [1]) (by simp) (by simp) rfl (netOf [0, w])
      (netOf_ok hnd hps)
    rw [show [1].map (pos (netOf [0, w]).reverse) = [w] from by
      simp only [List.map_cons, List.map_nil]; exact congrArg (· :: []) f1] at this
    exact this
  have fb : Derivable (theory (M + 3)) (placedBy (M + 3) (netOf [0, w])
      (mc (M + 3) .box [0] (ctlAt 1 true))) (mc (M + 3) .box [0] (ctlAt w true)) := by
    refine frameAt' ih hnd hps .box [0] [0] _ _ rfl (by simp) (by simp) (by simp [f0])
      (fun j hj => ?_)
    rcases j with _ | _ | j
    · simp [ctlAt, f0]; omega
    · simp [ctlAt, f1]
    · obtain ⟨h0, hw⟩ := hk (j + 1 + 1) (by omega) hj
      simp [ctlAt, hw]
  have k := via_frame hnd hps (l := [placeG (M + 3) (z : Circ 1) [1]])
    (r := [mc (M + 3) .box [0] (ctlAt 1 true)]) (List.Forall₂.cons fz List.Forall₂.nil)
    (List.Forall₂.cons fb List.Forall₂.nil) (by rw [drawn_one', drawn_one']; exact z1_box ih)
  rwa [drawn_one', drawn_one'] at k

/-- `Z` on a control wire passes a multi-controlled `(-1)ᵃ ZX` with every
control ((309) over every colouring, (346)). -/
theorem comm_zw (a : Bool) (y : ℕ → Bool) (w : ℕ) (hw1 : 1 ≤ w) (hwN : w < M + 3) :
    D.Comm (M + 3) (placeG (M + 3) (z : Circ 1) [w]) (mc (M + 3) (Kind.sgnZX a) [0] (colOn 1 (M + 3) y)) := by
  set S := (List.range (M + 3)).filter (fun j => decide (j ≠ 0 ∧ j ≠ w))
  have hnd : S.Nodup := (List.nodup_range).filter _
  have hmem : ∀ j, j ∈ S ↔ j < M + 3 ∧ j ≠ 0 ∧ j ≠ w := by
    intro j; simp [S, List.mem_filter, List.mem_range]
  have mB := mergeListB0 ih S (ctlAt w true) hnd (by rw [hmem]; omega)
    (fun x hx => ((hmem x).1 hx).1) (by simp [ctlAt]; omega)
  have eI : mc (M + 3) .box [0] (idleOn S (ctlAt w true)) = mc (M + 3) .box [0] (ctlAt w true) :=
    Net.mc_congr _ _ _ (fun j hj => by
      rw [idleOn_apply]
      by_cases hjS : j ∈ S
      · rw [if_pos hjS]; have := (hmem j).1 hjS; simp [ctlAt, this.2.2]
      · rw [if_neg hjS])
  rw [eI] at mB
  refine N13.Comm.congr ((zw_box ih w hw1 hwN).trans mB.symm).symm (Derivable.refl _)
    (N13.comm_drawn_left _ (fun g hg => ?_))
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hg
  have e : mc (M + 3) .box [0] (bitsOn S i (ctlAt w true)) =
      mc (M + 3) .box [0] (colOn 1 (M + 3) fun j => (bitsOn S i (ctlAt w true) j).getD false) :=
    Net.mc_congr _ _ _ (fun j hj => by
      by_cases hjS : j ∈ S
      · obtain ⟨b, hb⟩ := bitsOn_mem S i (ctlAt w true) j hjS
        have := (hmem j).1 hjS
        simp [hb, colOn, show 1 ≤ j by omega, hj]
      · rw [bitsOn_apply_not_mem hjS]
        rw [hmem] at hjS
        by_cases hj0 : j = 0
        · subst hj0; simp [ctlAt, colOn]; omega
        · have hjw : j = w := by omega
          subst hjw
          simp [ctlAt, colOn, bitsOn_apply_not_mem (show j ∉ S by rw [hmem]; omega), hw1, hj])
  rw [e]
  exact D.eq346 (M + 3) (by omega) ih _ _ a

end Ctl

/-- (359): conjugating a control on wire `w` of a multi-controlled `(-1)ᵃ ZX`
by the single-qubit `XZ` and `ZX` (in either order) exchanges its colour. -/
theorem eq359 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (a : Bool) (x : ℕ → Bool) (w : ℕ) (hw : 1 ≤ w)
    (hwN : w < N) (α : Bool) :
    Derivable (theory N)
      (drawn [xzAt N w, mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some α)), zxAt N w])
      (mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some !α))) ∧
    Derivable (theory N)
      (drawn [zxAt N w, mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some α)), xzAt N w])
      (mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some !α))) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  set G := mc (M + 3) (Kind.sgnZX a) [0] (setCtl (colOn 1 (M + 3) x) w (some α))
  set G' := mc (M + 3) (Kind.sgnZX a) [0] (setCtl (colOn 1 (M + 3) x) w (some !α))
  set Zw := placeG (M + 3) (z : Circ 1) [w]
  set Xw := placeG (M + 3) (QCert.RealCliffordCH.x : Circ 1) [w]
  have hX : Derivable (theory (M + 3)) Xw (xAt (M + 3) w) :=
    (place1_placeG QCert.RealCliffordCH.x (M + 3) w hwN).symm
  have h81 : Derivable (theory (M + 3)) (Xw * G * Xw) G' := by
    have := D.eq81 (M + 3) (Kind.sgnZX a) [0] (setCtl (colOn 1 (M + 3) x) w (some α)) w α hwN
      (by simp; omega) (by simp [setCtl])
    rw [conj3] at this
    refine (dmul (dmul hX (Derivable.refl _)) hX).trans (this.trans (der_of_eq ?_))
    exact Net.mc_congr _ _ _ (fun j hj => by simp only [setCtl]; split_ifs <;> rfl)
  have hxz : Derivable (theory (M + 3)) (xzAt (M + 3) w) (Xw * Zw) :=
    placeG_mul1 w hwN (QCert.RealCliffordCH.x : Circ 1) z
  have hzx : Derivable (theory (M + 3)) (zxAt (M + 3) w) (Zw * Xw) :=
    placeG_mul1 w hwN (z : Circ 1) QCert.RealCliffordCH.x
  have hZZ := zw_inv (N := M + 3) w hwN
  have colEq : ∀ β : Bool, ∀ j < M + 3, setCtl (colOn 1 (M + 3) x) w (some β) j =
      colOn 1 (M + 3) (fun i => if i = w then β else x i) j := fun β j hj => by
    simp only [setCtl, colOn]
    by_cases hjw : j = w
    · subst hjw; simp [hw, hj]
    · simp [hjw]
  have cG : ∀ β : Bool, D.Comm (M + 3) Zw (mc (M + 3) (Kind.sgnZX a) [0] (setCtl (colOn 1 (M + 3) x) w (some β))) := by
    intro β
    rw [Net.mc_congr _ _ _ (colEq β)]
    exact comm_zw ih a _ w hw hwN
  have pass : ∀ g : Circ (M + 3), D.Comm (M + 3) Zw g → Derivable (theory (M + 3)) (Zw * g * Zw) g := by
    intro g hg
    unfold D.Comm at hg
    rw [drawn_two', drawn_two'] at hg
    have := dright Zw hg
    refine this.symm.trans ?_
    rw [mul_assoc]; have := dleft g hZZ; rwa [mul_one] at this
  constructor
  · rw [drawn_three']
    -- `(Z X) G (X Z) = Z (X G X) Z = Z G' Z = G'`
    refine (dmul (dmul hzx (Derivable.refl _)) hxz).trans ?_
    have e : Zw * Xw * G * (Xw * Zw) = Zw * (Xw * G * Xw) * Zw := by simp only [mul_assoc]
    rw [e]
    exact (dright _ (dleft _ h81)).trans (pass G' (cG (!α)))
  · rw [drawn_three']
    refine (dmul (dmul hxz (Derivable.refl _)) hzx).trans ?_
    have e : Xw * Zw * G * (Zw * Xw) = Xw * (Zw * G * Zw) * Xw := by simp only [mul_assoc]
    rw [e]
    exact (dright _ (dleft _ (pass G (cG α)))).trans h81

end QCert.RealCliffordCH.Sec8.D.N15
