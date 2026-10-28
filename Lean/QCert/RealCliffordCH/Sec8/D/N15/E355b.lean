/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (355): the statement

See `E355.lean` for the argument.
-/
import QCert.RealCliffordCH.Sec8.D.N15.E355

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

theorem idleOn_apply : ∀ (ws : List ℕ) (base : ℕ → Option Bool) (j : ℕ),
    idleOn ws base j = if j ∈ ws then none else base j
  | [], base, j => by simp [idleOn]
  | w :: ws, base, j => by
    simp only [idleOn, idleOn_apply ws, setCtl, List.mem_cons]
    by_cases h1 : j ∈ ws <;> by_cases h2 : j = w <;> simp [h1, h2]

theorem bitsOn_apply_not_mem {ws : List ℕ} {i : ℕ} {base : ℕ → Option Bool} {j : ℕ}
    (hj : j ∉ ws) : bitsOn ws i base j = base j := bitsOn_of_not_mem ws i base j hj

/-- The box on wire `1`, black on `0, 2, …` (the box of (305)). -/
abbrev B5 (M : ℕ) : Circ (M + 3) := mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))

/-- The wires `2, …, M + 2`. -/
abbrev S5 (M : ℕ) : List ℕ := (List.range (M + 1)).map (· + 2)

/-- A colouring read through a frame. -/
def pullC (ps : List ℕ) (x : ℕ → Bool) : ℕ → Bool := fun i => x (frm ps i)

section Sq

variable {M : ℕ}

theorem S5_nodup : (S5 M).Nodup :=
  List.Nodup.map (fun a b h => by simpa using h) List.nodup_range

theorem mem_S5 {j : ℕ} : j ∈ S5 M ↔ 2 ≤ j ∧ j < M + 3 := by
  simp only [S5, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨j - 2, by omega, by omega⟩

/-- The colours of the `i`-th colouring of the wires `2, …`, wire `1` black. -/
def col5 (M i : ℕ) : ℕ → Bool := fun j => (bitsOn (S5 M) i (ctlAt 1 true) j).getD false

theorem bitsOn5 (i : ℕ) : ∀ j < M + 3, bitsOn (S5 M) i (ctlAt 1 true) j = colOn 1 (M + 3) (col5 M i) j := by
  intro j hj
  by_cases hjS : j ∈ S5 M
  · obtain ⟨b, hb⟩ := bitsOn_mem (S5 M) i (ctlAt 1 true) j hjS
    have h2 := (mem_S5.1 hjS)
    simp [col5, hb, colOn, show 1 ≤ j by omega, hj]
  · rw [bitsOn_apply_not_mem hjS]
    have : j = 0 ∨ j = 1 := by rw [mem_S5] at hjS; omega
    rcases this with rfl | rfl
    · simp [colOn, ctlAt]
    · simp [col5, colOn, ctlAt, bitsOn_apply_not_mem hjS]

variable (ih : IH (M + 3))
include ih

/-- The box `B5` is an involution ((311) moved to wire `1`). -/
theorem B5_inv : Derivable (theory (M + 3)) (drawn [B5 M, B5 M]) 1 := by
  have h := D.eq311 (M + 3) (by omega) ih (fun _ => true)
  have hS := swsw (M + 3) 0 (by omega)
  have mv : Derivable (theory (M + 3))
      (swAt (M + 3) 0 * mc (M + 3) .box [0] (colOn 1 (M + 3) fun _ => true) * swAt (M + 3) 0) (B5 M) := by
    have := mcSwapBH ih 0 (by omega) .box (Or.inl rfl) [0] (colOn 1 (M + 3) fun _ => true) rfl
      (by simp) (by simp)
    rw [conj3] at this
    refine this.trans (der_of_eq ?_)
    rw [show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Function.comp, Net.tau, colOn, ctlOr, ctlAt, blackOn] <;> omega
  have k := via_conj hS (l := [mc (M + 3) .box [0] (colOn 1 (M + 3) fun _ => true),
      mc (M + 3) .box [0] (colOn 1 (M + 3) fun _ => true)]) (R := [])
    (List.Forall₂.cons mv (List.Forall₂.cons mv List.Forall₂.nil)) List.Forall₂.nil
    (by simpa [drawn] using h)
  simpa [drawn] using k

/-- (347): a gate with a white control on a wire `≥ 2` passes `B5`. -/
theorem comm_B5 (a : Bool) (x : ℕ → Bool) (hx1 : x 1 = true) (j : ℕ) (hj2 : 2 ≤ j)
    (hjN : j < M + 3) (hxj : x j = false) :
    D.Comm (M + 3) (mc (M + 3) (Kind.sgnZX a) [0] (colOn 1 (M + 3) x)) (B5 M) := by
  have hnd : [1, 0].Nodup := by decide
  have hps : ∀ p ∈ [1, 0], p < M + 3 := by simp
  have f0 : frm [1, 0] 0 = 1 := frm_getD hnd hps (by simp)
  have f1 : frm [1, 0] 1 = 0 := frm_getD hnd hps (by simp)
  have hk : ∀ i, i < 2 ↔ i ∈ [1, 0] := by intro i; simp; omega
  have fB : Derivable (theory (M + 3)) (placedBy (M + 3) (netOf [1, 0])
      (mc (M + 3) .box [0] (ctlOr (ctlAt 1 true) (colOn 2 (M + 3) fun _ => true)))) (B5 M) := by
    refine frameAt' ih hnd hps .box [0] [1] _ _ rfl (by simp) (by simp) (by simp [f0])
      (fun i hi => ?_)
    rcases i with _ | _ | i
    · simp [ctlOr, ctlAt, colOn, blackOn, f0]
    · simp [ctlOr, ctlAt, colOn, blackOn, f1]
    · obtain ⟨h2, hl⟩ := frm_ge hnd hps 2 hk (j := i + 1 + 1) (by simp) hi
      generalize frm [1, 0] (i + 1 + 1) = f at h2 hl ⊢
      simp [ctlOr, ctlAt, colOn, blackOn, hi, hl, show f ≠ 0 by omega, show 2 ≤ f by omega]
  have fZ : Derivable (theory (M + 3)) (placedBy (M + 3) (netOf [1, 0])
      (mc (M + 3) (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 true) (colOn 2 (M + 3) (pullC [1, 0] x)))))
      (mc (M + 3) (Kind.sgnZX a) [0] (colOn 1 (M + 3) x)) := by
    refine frameAt' ih hnd hps (Kind.sgnZX a) [1] [0] _ _ (by simp [kindSp_sgnZX]) (by simp)
      (by simp) (by simp [f1]) (fun i hi => ?_)
    rcases i with _ | _ | i
    · simp [ctlOr, ctlAt, colOn, f0, hx1]
    · simp [ctlOr, ctlAt, colOn, f1]
    · obtain ⟨h2, hl⟩ := frm_ge hnd hps 2 hk (j := i + 1 + 1) (by simp) hi
      simp only [ctlOr, ctlAt, colOn, pullC]
      generalize frm [1, 0] (i + 1 + 1) = f at h2 hl ⊢
      simp [hi, hl, show 1 ≤ f by omega]
  obtain ⟨hp2, hpN⟩ := pos_ge hnd hps (w := j) hjN (by simp; omega)
  have hd : DiffOn 2 (M + 3) (fun _ => true) (pullC [1, 0] x) :=
    ⟨_, by simpa using hp2, hpN, by simp [pullC, frm_pos, hxj]⟩
  exact (comm_frame hnd hps fB fZ (D.eq347 (M + 3) (by omega) ih _ _ hd a true true)).symm

end Sq

end QCert.RealCliffordCH.Sec8.D.N15
