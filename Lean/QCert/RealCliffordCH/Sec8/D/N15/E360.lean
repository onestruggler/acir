/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (360): `P ⊗ P` on the target and the idle wire turns `ZX` into `XZ`

Not the paper's route.  On `N = m + 4` wires write `a` for the `ZX` on wire
`1` (controls `2, …` black, wire `0` idle), `a'` for the `XZ`, `P` for
`P ⊗ P` on the wires `0, 1` and `S` for the swap of the wires `2, 3`.

* (333) and (334) one width down, carried past the idle wire `0`
  (`Net.liftIdle`), write `a` and `a'` with the multi-controlled `H` on the
  wires `3, 1` and the box on wire `2`; their box wires are idle wires of
  the other gates and move to wire `0` by (277) and (274) in a frame:
  `a = H₁ B₁ H₁ B₁` and `a' = B₁ H₁ B₁ H₁` (drawn), with
  `H₁ = hg[0,1](2, 4, …)` and `B₁ = box[0](1, 3, 4, …)`.
* `P` conjugates `H₁` into `B₂ = box[0](1, 2, 4, …)` and `B₁` into
  `H₂ = hg[0,1](3, 4, …)`: on the wires other than the idle `3`, resp. `2`,
  this is Definition 2.4 (`N13.hg_box`; on three wires a semantic step).
* `S` conjugates `H₁`, `B₁` into the same `H₂`, `B₂` and fixes `a'`
  ((353), through `mcSwapAll'`).  So `P a P = B₂ H₂ B₂ H₂ = S a' S = a'`.

On three wires (360) is (129).  Every step was checked numerically at
`N = 4, 5, 6` (`gen/sec8/e/m360b.py`).
-/
import QCert.RealCliffordCH.Sec8.D.N15.Swap
import QCert.RealCliffordCH.Sec8.D.Small
import QCert.RealCliffordCH.Sec8.D.W3.Tokens

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-! ## Tools -/


/-- `ToTop.mc` with the targets and controls of the result given. -/
theorem toTop_mc' {M q : ℕ} (hqM : q ≤ M) (K : Kind) (tg tg' : List ℕ) (c c' : ℕ → Option Bool)
    (htg : tg.length = kindSp K) (hnd : tg.Nodup) (htgM : ∀ t ∈ tg, t ≤ M) (hqt : q ∉ tg)
    (hcq : c q = none) (htg' : tg.map (dropW q) = tg') (hc : ∀ j < M, c (liftW q j) = c' j) :
    ToTop M q (mc (M + 1) K tg c) (mc M K tg' c') := by
  have h := ToTop.mc hqM K tg c htg hnd htgM hqt hcq
  rwa [htg', Net.mc_congr M K tg' (c := c ∘ liftW q) (c' := c') hc] at h

/-- `P ⊗ P` on the wires `0, 1` moved past an idle wire `q ≥ 2`. -/
theorem toTop_pp {M q : ℕ} (hq : 2 ≤ q) (hqM : q ≤ M) :
    ToTop M q (ppAt (M + 1) 0 1) (ppAt M 0 1) := by
  unfold ToTop
  have e : ([0, 1] : List ℕ).map (dropW q) = [0, 1] := by
    simp only [List.map_cons, List.map_nil, dropW]
    rw [if_pos (by omega), if_pos (by omega)]
  refine gate_toTop (pp : Circ 2) (ps := [0, 1]) (by simp) (fun p hp => by simp at hp; omega) rfl
    q hqM (by simp <;> omega) (Derivable.refl _) ?_
  rw [e]; exact Derivable.refl _

theorem ppAt_eq (k : ℕ) : ppAt (k + 2) 0 1 = (pp : Circ (k + 2)) := by
  rw [← N8.atBot_pp (k + 2) k le_rfl, atBot_self]

/-- `P ⊗ P` on the wires `0, 1` conjugates the box on wire `0` into the
multi-controlled `H` (Definition 2.4; on three wires, Lemma 5.1). -/
theorem pp_box (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 3)) ((pp : Circ (m + 3)) * D.Bx (m + 3) * pp)
      (mc (m + 3) .hg [0, 1] (blackOn 2 (m + 3))) := by
  rcases m with _ | m
  · exact ih 3 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  · have h := N13.hg_box m (fun _ => true)
    have e1 : mc (m + 2 + 2) .hg [0, 1] (colOn 2 (m + 2 + 2) fun _ => true) =
        mc (m + 1 + 3) .hg [0, 1] (blackOn 2 (m + 1 + 3)) :=
      Net.mc_congr _ _ _ (fun j hj => by simp [colOn, blackOn])
    have e2 : mc (m + 2 + 2) .box [0] (colOn 1 (m + 2 + 2) (N13.hgCol fun _ => true)) =
        D.Bx (m + 1 + 3) :=
      Net.mc_congr _ _ _ (fun j hj => by simp [colOn, blackOn, N13.hgCol])
    rw [e1, e2] at h
    rw [mul_assoc]
    exact h.symm

/-- The inverse direction. -/
theorem pp_hg (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 3)) ((pp : Circ (m + 3)) * mc (m + 3) .hg [0, 1] (blackOn 2 (m + 3)) * pp)
      (D.Bx (m + 3)) := by
  have hp : Derivable (theory (m + 3)) ((pp : Circ (m + 3)) * pp) 1 :=
    N13.pp_inv m (ih.mono (by omega))
  have h := pp_box m ih
  refine (dright _ (dleft _ h.symm)).trans ?_
  have e : (pp : Circ (m + 3)) * (pp * D.Bx (m + 3) * pp) * pp = (pp * pp) * D.Bx (m + 3) * (pp * pp) := by
    simp only [mul_assoc]
  rw [e]
  have := dmul (dmul hp (Derivable.refl (D.Bx (m + 3)))) hp
  simpa using this

/-! ## The gates -/

section Gates

variable (m : ℕ)

/-- The controls of `H₀`, `H₁`: black on `2, 4, …`. -/
abbrev cH360 : ℕ → Option Bool := ctlOr (ctlAt 2 true) (blackOn 4 (m + 4))
/-- The controls of `B₀`, `B₁`: black on `1, 3, …`. -/
abbrev cB360 : ℕ → Option Bool := ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))
abbrev a360 : Circ (m + 4) := mc (m + 4) .zx [1] (blackOn 2 (m + 4))
abbrev a360' : Circ (m + 4) := mc (m + 4) .xz [1] (blackOn 2 (m + 4))
abbrev H360a : Circ (m + 4) := mc (m + 4) .hg [3, 1] (cH360 m)
abbrev B360a : Circ (m + 4) := mc (m + 4) .box [2] (cB360 m)
abbrev H360b : Circ (m + 4) := mc (m + 4) .hg [0, 1] (cH360 m)
abbrev B360b : Circ (m + 4) := mc (m + 4) .box [0] (cB360 m)
abbrev H360c : Circ (m + 4) := mc (m + 4) .hg [0, 1] (blackOn 3 (m + 4))
abbrev B360c : Circ (m + 4) :=
  mc (m + 4) .box [0] (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 true) (blackOn 4 (m + 4))))

end Gates

/-- Pointwise equality of two control assignments: unfold and split. -/
macro "ctl_tac" : tactic => `(tactic| (simp only [liftW, cH360, cB360, ctlOr, ctlAt, blackOn,
  colOn, setCtl, Function.comp, Net.tau]; split_ifs <;> first | rfl | (exfalso; omega)))

section Chain

variable {m : ℕ} (ih : IH (m + 4))
include ih

/-- (333) one width down, past the idle wire `0`. -/
theorem lift333 : Derivable (theory (m + 4)) (a360 m) (drawn [H360a m, B360a m, H360a m, B360a m]) := by
  have h := D.eq333 (m + 3) (by omega) (ih.mono (by omega))
  have tZ : ToTop (m + 3) 0 (a360 m) (mc (m + 3) .zx [0] (blackOn 1 (m + 3))) :=
    toTop_mc' (by omega) .zx [1] [0] _ _ rfl (by simp) (by simp) (by simp) (by simp [blackOn])
      (by simp [dropW]) (fun j hj => by simp [liftW, blackOn] <;> omega)
  have tH : ToTop (m + 3) 0 (H360a m) (mc (m + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 3)))) :=
    toTop_mc' (by omega) .hg [3, 1] [2, 0] _ _ rfl (by simp) (by simp <;> omega) (by simp)
      (by simp [cH360, cB360, ctlOr, ctlAt, blackOn]) (by simp [dropW]) (fun j hj => by
        ctl_tac)
  have tB : ToTop (m + 3) 0 (B360a m) (mc (m + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 3)))) :=
    toTop_mc' (by omega) .box [2] [1] _ _ rfl (by simp) (by simp <;> omega) (by simp)
      (by simp [cH360, cB360, ctlOr, ctlAt, blackOn]) (by simp [dropW]) (fun j hj => by
        ctl_tac)
  exact liftIdle tZ (ToTop.ofList (.cons tH (.cons tB (.cons tH (.cons tB .nil))))) h

/-- (334) one width down, past the idle wire `0`. -/
theorem lift334 : Derivable (theory (m + 4)) (a360' m) (drawn [B360a m, H360a m, B360a m, H360a m]) := by
  have h := D.eq334 (m + 3) (by omega) (ih.mono (by omega))
  have tZ : ToTop (m + 3) 0 (a360' m) (mc (m + 3) .xz [0] (blackOn 1 (m + 3))) :=
    toTop_mc' (by omega) .xz [1] [0] _ _ rfl (by simp) (by simp) (by simp) (by simp [blackOn])
      (by simp [dropW]) (fun j hj => by simp [liftW, blackOn] <;> omega)
  have tH : ToTop (m + 3) 0 (H360a m) (mc (m + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 3)))) :=
    toTop_mc' (by omega) .hg [3, 1] [2, 0] _ _ rfl (by simp) (by simp <;> omega) (by simp)
      (by simp [cH360, cB360, ctlOr, ctlAt, blackOn]) (by simp [dropW]) (fun j hj => by
        ctl_tac)
  have tB : ToTop (m + 3) 0 (B360a m) (mc (m + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 3)))) :=
    toTop_mc' (by omega) .box [2] [1] _ _ rfl (by simp) (by simp <;> omega) (by simp)
      (by simp [cH360, cB360, ctlOr, ctlAt, blackOn]) (by simp [dropW]) (fun j hj => by
        ctl_tac)
  exact liftIdle tZ (ToTop.ofList (.cons tB (.cons tH (.cons tB (.cons tH .nil))))) h

/-- (277) in the frame `[0, 3, 1]`: the box wire of `H₀` moves to wire `0`. -/
theorem moveH360 : Derivable (theory (m + 4)) (H360a m) (H360b m) := by
  have hnd : [0, 3, 1].Nodup := by decide
  have hps : ∀ p ∈ [0, 3, 1], p < m + 4 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 3, 1] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 3, 1] 1 = 3 := frm_getD hnd hps (by simp)
  have f2 : frm [0, 3, 1] 2 = 1 := frm_getD hnd hps (by simp)
  have hpt : ∀ j < m + 4, blackOn 3 (m + 4) j = cH360 m (frm [0, 3, 1] j) := by
    intro j hj
    rcases j with _ | _ | _ | j
    · simp [f0, ctlOr, ctlAt, blackOn]
    · simp [f1, ctlOr, ctlAt, blackOn]
    · simp [f2, ctlOr, ctlAt, blackOn]
    · obtain ⟨hm, hl⟩ := frm_out' hnd hps (j := j + 3) (by simp) hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      by_cases h2 : frm [0, 3, 1] (j + 3) = 2
      · rw [h2]; simp [ctlOr, ctlAt, blackOn]; omega
      · have h4 : 4 ≤ frm [0, 3, 1] (j + 3) := by omega
        simp [ctlOr, ctlAt, blackOn, h2, h4, hl]; omega
  have fA := frameAt' ih hnd hps .hg [1, 2] [3, 1] (cH360 m) (blackOn 3 (m + 4)) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f1, f2]) hpt
  have fB := frameAt' ih hnd hps .hg [0, 2] [0, 1] (cH360 m) (blackOn 3 (m + 4)) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f2]) hpt
  have k := via_frame hnd hps (l := [_]) (r := [_]) (List.Forall₂.cons fA List.Forall₂.nil)
    (List.Forall₂.cons fB List.Forall₂.nil)
    (by rw [drawn_one', drawn_one']; exact D.eq277 (m + 4) (by omega) ih)
  rwa [drawn_one', drawn_one'] at k

/-- (274) in the frame `[0, 2]`: the box wire of `B₀` moves to wire `0`. -/
theorem moveB360 : Derivable (theory (m + 4)) (B360a m) (B360b m) := by
  have hnd : [0, 2].Nodup := by decide
  have hps : ∀ p ∈ [0, 2], p < m + 4 := by intro p hp; simp at hp; omega
  have f0 : frm [0, 2] 0 = 0 := frm_getD hnd hps (by simp)
  have f1 : frm [0, 2] 1 = 2 := frm_getD hnd hps (by simp)
  have hpt : ∀ j < m + 4, blackOn 2 (m + 4) j = cB360 m (frm [0, 2] j) := by
    intro j hj
    rcases j with _ | _ | j
    · simp [f0, ctlOr, ctlAt, blackOn]
    · simp [f1, ctlOr, ctlAt, blackOn]
    · obtain ⟨hm, hl⟩ := frm_out' hnd hps (j := j + 2) (by simp) hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      by_cases h1 : frm [0, 2] (j + 2) = 1
      · rw [h1]; simp [ctlOr, ctlAt, blackOn]; omega
      · have h3 : 3 ≤ frm [0, 2] (j + 2) := by omega
        simp [ctlOr, ctlAt, blackOn, h1, h3, hl]; omega
  have fA := frameAt' ih hnd hps .box [1] [2] (cB360 m) (blackOn 2 (m + 4)) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f1]) hpt
  have fB := frameAt' ih hnd hps .box [0] [0] (cB360 m) (blackOn 2 (m + 4)) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0]) hpt
  have k := via_frame hnd hps (l := [_]) (r := [_]) (List.Forall₂.cons fA List.Forall₂.nil)
    (List.Forall₂.cons fB List.Forall₂.nil)
    (by rw [drawn_one', drawn_one']; exact D.eq274 (m + 4) (by omega) ih)
  rwa [drawn_one', drawn_one'] at k

/-- `P H₁ P = B₂`, on the wires other than the idle `3`. -/
theorem ppH360 : Derivable (theory (m + 4))
    (ppAt (m + 4) 0 1 * H360b m * ppAt (m + 4) 0 1) (B360c m) := by
  have tP := toTop_pp (M := m + 3) (q := 3) (by omega) (by omega)
  have tH : ToTop (m + 3) 3 (H360b m) (mc (m + 3) .hg [0, 1] (blackOn 2 (m + 3))) :=
    toTop_mc' (by omega) .hg [0, 1] [0, 1] _ _ rfl (by simp) (by simp <;> omega) (by simp)
      (by simp [cH360, cB360, ctlOr, ctlAt, blackOn]) (by simp [dropW]) (fun j hj => by
        ctl_tac)
  have tB : ToTop (m + 3) 3 (B360c m) (D.Bx (m + 3)) :=
    toTop_mc' (by omega) .box [0] [0] _ _ rfl (by simp) (by simp) (by simp)
      (by simp [cH360, cB360, ctlOr, ctlAt, blackOn]) (by simp [dropW]) (fun j hj => by
        ctl_tac)
  have d := pp_hg m ih
  rw [← ppAt_eq (m + 1)] at d
  exact liftIdle ((tP.mul tH).mul tP) tB d

/-- `P B₁ P = H₂`, on the wires other than the idle `2`. -/
theorem ppB360 : Derivable (theory (m + 4))
    (ppAt (m + 4) 0 1 * B360b m * ppAt (m + 4) 0 1) (H360c m) := by
  have tP := toTop_pp (M := m + 3) (q := 2) (by omega) (by omega)
  have tB : ToTop (m + 3) 2 (B360b m) (D.Bx (m + 3)) :=
    toTop_mc' (by omega) .box [0] [0] _ _ rfl (by simp) (by simp) (by simp)
      (by simp [cH360, cB360, ctlOr, ctlAt, blackOn]) (by simp [dropW]) (fun j hj => by
        ctl_tac)
  have tH : ToTop (m + 3) 2 (H360c m) (mc (m + 3) .hg [0, 1] (blackOn 2 (m + 3))) :=
    toTop_mc' (by omega) .hg [0, 1] [0, 1] _ _ rfl (by simp) (by simp <;> omega) (by simp)
      (by simp [blackOn]) (by simp [dropW]) (fun j hj => by
        ctl_tac)
  have d := pp_box m ih
  rw [← ppAt_eq (m + 1)] at d
  exact liftIdle ((tP.mul tB).mul tP) tH d

/-- The swap of the wires `2, 3` carries `H₁` to `H₂`, `B₁` to `B₂` and fixes
`a'`. -/
theorem swH360 : Derivable (theory (m + 4))
    (swAt (m + 4) 2 * H360b m * swAt (m + 4) 2) (H360c m) := by
  have h := mcSwapAll' ih 2 (by omega) .hg [0, 1] (cH360 m) rfl (by simp) (by simp)
  rw [conj3] at h
  refine h.trans (der_of_eq ?_)
  rw [show ([0, 1] : List ℕ).map (Net.tau 2) = [0, 1] by simp [Net.tau]]
  refine Net.mc_congr _ _ _ (fun j hj => ?_)
  rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;> omega

theorem swB360 : Derivable (theory (m + 4))
    (swAt (m + 4) 2 * B360b m * swAt (m + 4) 2) (B360c m) := by
  have h := mcSwapAll' ih 2 (by omega) .box [0] (cB360 m) rfl (by simp) (by simp)
  rw [conj3] at h
  refine h.trans (der_of_eq ?_)
  rw [show ([0] : List ℕ).map (Net.tau 2) = [0] by simp [Net.tau]]
  refine Net.mc_congr _ _ _ (fun j hj => ?_)
  rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;> omega

theorem swA360 : Derivable (theory (m + 4))
    (swAt (m + 4) 2 * a360' m * swAt (m + 4) 2) (a360' m) := by
  have h := mcSwapAll' ih 2 (by omega) .xz [1] (blackOn 2 (m + 4)) rfl (by simp) (by simp)
  rw [conj3] at h
  refine h.trans (der_of_eq ?_)
  rw [show ([1] : List ℕ).map (Net.tau 2) = [1] by simp [Net.tau]]
  refine Net.mc_congr _ _ _ (fun j hj => ?_)
  rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, blackOn] <;> omega

/-- (360) from four wires on. -/
theorem eq360_ge4 : Derivable (theory (m + 4))
    (drawn [ppAt (m + 4) 0 1, a360 m]) (drawn [a360' m, ppAt (m + 4) 0 1]) := by
  set P := ppAt (m + 4) 0 1
  have hP : Derivable (theory (m + 4)) (P * P) 1 := by
    rw [show P = (pp : Circ (m + 2 + 2)) from ppAt_eq (m + 2)]
    exact N13.pp_inv (m + 1) (ih.mono (by omega))
  have hS := swsw (m + 4) 2 (by omega)
  -- `a = H₁ B₁ H₁ B₁`, `a' = B₁ H₁ B₁ H₁`
  have mH := moveH360 ih
  have mB := moveB360 ih
  have ha : Derivable (theory (m + 4)) (a360 m) (drawn [H360b m, B360b m, H360b m, B360b m]) :=
    (lift333 ih).trans (drawn_forall2 (.cons mH (.cons mB (.cons mH (.cons mB .nil)))))
  have ha' : Derivable (theory (m + 4)) (a360' m) (drawn [B360b m, H360b m, B360b m, H360b m]) :=
    (lift334 ih).trans (drawn_forall2 (.cons mB (.cons mH (.cons mB (.cons mH .nil)))))
  -- conjugation by `P` and by the swap
  have kP := via_conj hP (l := [a360 m]) (L := [P * a360 m * P])
    (List.Forall₂.cons (Derivable.refl _) List.Forall₂.nil)
    (List.Forall₂.cons (ppH360 ih) (List.Forall₂.cons (ppB360 ih) (List.Forall₂.cons (ppH360 ih)
      (List.Forall₂.cons (ppB360 ih) List.Forall₂.nil)))) (by rw [drawn_one']; exact ha)
  have kS := via_conj hS (l := [a360' m]) (L := [a360' m])
    (List.Forall₂.cons (swA360 ih) List.Forall₂.nil)
    (List.Forall₂.cons (swB360 ih) (List.Forall₂.cons (swH360 ih) (List.Forall₂.cons (swB360 ih)
      (List.Forall₂.cons (swH360 ih) List.Forall₂.nil)))) (by rw [drawn_one']; exact ha')
  rw [drawn_one'] at kP kS
  have key : Derivable (theory (m + 4)) (P * a360 m * P) (a360' m) := kP.trans kS.symm
  -- `a P = P (P a P)`
  rw [drawn_two', drawn_two']
  have e : P * (P * a360 m * P) = (P * P) * (a360 m * P) := by simp only [mul_assoc]
  refine (?_ : Derivable _ _ (P * (P * a360 m * P))).trans (dleft P key)
  rw [e]
  have := dright (a360 m * P) hP
  rw [one_mul] at this
  exact this.symm

end Chain

/-! ## Three wires: (129) -/

section Three

open WE WS
open Eng (L)

def ppL3 : List L := [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0]
def zxL3 : List L := [L.K 1, L.S 1, L.Z 2, L.S 1, L.K 1, L.S 1, L.Z 2, L.S 1]
def xzL3 : List L := [L.S 1, L.Z 2, L.S 1, L.K 1, L.S 1, L.Z 2, L.S 1, L.K 1]

def L360 : List Tk := [Tk.p 2 ppL3 [0, 1], Tk.g .zx [1] [(2, true)]]
def R360 : List Tk := [Tk.g .xz [1] [(2, true)], Tk.p 2 ppL3 [0, 1]]
def T360 : WE.Tbl := [((ppL3 ++ zxL3).map Tk.s, (xzL3 ++ ppL3).map Tk.s)]

theorem run360 : check 2 T360 L360 R360
    [.sem 0 1 (ppL3.map Tk.s) 2,
     .sem 10 1 (zxL3.map Tk.s) 0,
     .rw 0 0 false,
     .sem 0 8 [Tk.g .xz [1] [(2, true)]] 0,
     .sem 1 10 [Tk.p 2 ppL3 [0, 1]] 2] = true := by
  decide +kernel

theorem eq360_3 (ih : IH 3) :
    Derivable (theory 3) (drawn [ppAt 3 0 1, mc 3 .zx [1] (blackOn 2 3)])
      (drawn [mc 3 .xz [1] (blackOn 2 3), ppAt 3 0 1]) := by
  have h129 := eq129 0 ih
  rw [N8.pad_zero3, N8.pad_zero3] at h129
  have h0 : Derivable (theory 3) (wcT 3 ((ppL3 ++ zxL3).map Tk.s)) (wcT 3 ((xzL3 ++ ppL3).map Tk.s)) := by
    rw [← circW_eq_wcT, ← circW_eq_wcT]; exact h129
  have hT : WE.AllD 3 T360 := WE.AllD.cons h0 (WE.AllD.nil 3)
  have k := check_sound ih hT run360
  have eL : wcT 3 L360 = drawn [ppAt 3 0 1, mc 3 .zx [1] (blackOn 2 3)] := by
    show drawn [placeG 3 (circW 2 ppL3) [0, 1], mc 3 .zx [1] (SE.ctl 3 [(2, true)] false)] = _
    rw [Net.mc_congr 3 .zx [1] (c := SE.ctl 3 [(2, true)] false) (c' := blackOn 2 3) (fun j hj => by
      rcases j with _ | _ | _ | j <;> simp [SE.ctl, blackOn] <;> omega)]
    rfl
  have eR : wcT 3 R360 = drawn [mc 3 .xz [1] (blackOn 2 3), ppAt 3 0 1] := by
    show drawn [mc 3 .xz [1] (SE.ctl 3 [(2, true)] false), placeG 3 (circW 2 ppL3) [0, 1]] = _
    rw [Net.mc_congr 3 .xz [1] (c := SE.ctl 3 [(2, true)] false) (c' := blackOn 2 3) (fun j hj => by
      rcases j with _ | _ | _ | j <;> simp [SE.ctl, blackOn] <;> omega)]
    rfl
  rwa [eL, eR] at k

end Three

end QCert.RealCliffordCH.Sec8.D.N15
