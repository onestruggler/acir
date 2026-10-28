/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The small-width cases of (310)

With four wires, removing a control leaves just one control on the
Hadamard. Its expression as P⊗P around a box is then a three-wire
semantic step. The two-control factors use `hgPP` as usual.
-/
import QCert.RealCliffordCH.Sec8.D.N8.Low

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

set_option maxRecDepth 100000

private def ppTk : WE.Tk := .p 2
  [.K 0, .H 1, .Z 0, .K 0, .H 1, .Z 0, .K 0, .H 1, .Z 0, .S 0] [0, 1]

private theorem hgPP_single4 (ih : IH 4) (j : ℕ) (hj : j = 2 ∨ j = 3) (b : Bool) :
    Derivable (theory 4) (mc 4 .hg [0, 1] (ctl 4 [(j, b)] false))
      (drawn [ppAt 4 0 1, mc 4 .box [0] (ctl 4 [(1, true), (j, b)] false), ppAt 4 0 1]) := by
  have h := WE.check_sound ih (WE.AllD.nil 4)
    (w := [.g .hg [0, 1] [(j, b)]])
    (v := [ppTk, .g .box [0] [(1, true), (j, b)], ppTk])
    (ss := [.sem 0 1 [ppTk, .g .box [0] [(1, true), (j, b)], ppTk] (5 - j)])
    (by rcases hj with rfl | rfl <;> cases b <;> decide +kernel)
  have he : WE.wcT 4 [.g .hg [0, 1] [(j, b)]] =
      mc 4 .hg [0, 1] (ctl 4 [(j, b)] false) := by
    simp [WE.wcT, WE.Tk.circ, drawn]
  rw [he] at h
  exact h

private theorem hgPP_none4 (ih : IH 4) (x : ℕ → Bool) (w : ℕ)
    (hw : 2 ≤ w) (hwN : w < 4) :
    Derivable (theory 4) (mc 4 .hg [0, 1] (setCtl (colOn 2 4 x) w none))
      (drawn [ppAt 4 0 1,
        mc 4 .box [0] (setCtl (colOn 1 4 (fun i => if i = 1 then true else x i)) w none),
        ppAt 4 0 1]) := by
  let j := 5 - w
  have hj : j = 2 ∨ j = 3 := by dsimp [j]; omega
  have eH : mc 4 .hg [0, 1] (setCtl (colOn 2 4 x) w none) =
      mc 4 .hg [0, 1] (ctl 4 [(j, x j)] false) := by
    apply mc_congr
    intro i hi
    rcases (by omega : w = 2 ∨ w = 3) with rfl | rfl <;>
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      simp [j, setCtl, colOn, ctl] <;> rfl
  have eB : mc 4 .box [0]
      (setCtl (colOn 1 4 (fun i => if i = 1 then true else x i)) w none) =
      mc 4 .box [0] (ctl 4 [(1, true), (j, x j)] false) := by
    apply mc_congr
    intro i hi
    rcases (by omega : w = 2 ∨ w = 3) with rfl | rfl <;>
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      simp [j, setCtl, colOn, ctl] <;> rfl
  rw [eH, eB]
  exact hgPP_single4 ih j hj (x j)

theorem eq310_3 (ih : IH 3) (x : ℕ → Bool) (w : ℕ)
    (hw : 2 ≤ w) (hwN : w < 3) (b : Bool) :
    Derivable (theory 3)
      (drawn [mc 3 .hg [0, 1] (setCtl (colOn 2 3 x) w (some b)),
        mc 3 .hg [0, 1] (setCtl (colOn 2 3 x) w (some !b))])
      (mc 3 .hg [0, 1] (setCtl (colOn 2 3 x) w none)) := by
  obtain rfl : w = 2 := by omega
  cases b
  · exact t310 ih false
  · exact t310 ih true

theorem eq310_4 (ih : IH 4)
    (h309 : ∀ (x : ℕ → Bool) (w : ℕ), 1 ≤ w → w < 4 → ∀ b : Bool,
      Derivable (theory 4)
        (drawn [mc 4 .box [0] (setCtl (colOn 1 4 x) w (some b)),
          mc 4 .box [0] (setCtl (colOn 1 4 x) w (some !b))])
        (mc 4 .box [0] (setCtl (colOn 1 4 x) w none)))
    (x : ℕ → Bool) (w : ℕ) (hw : 2 ≤ w) (hwN : w < 4) (b : Bool) :
    Derivable (theory 4)
      (drawn [mc 4 .hg [0, 1] (setCtl (colOn 2 4 x) w (some b)),
        mc 4 .hg [0, 1] (setCtl (colOn 2 4 x) w (some !b))])
      (mc 4 .hg [0, 1] (setCtl (colOn 2 4 x) w none)) := by
  set x' : ℕ → Bool := fun i => if i = 1 then true else x i
  have hv : ∀ v : Option Bool,
      Derivable (theory 4) (mc 4 .hg [0, 1] (setCtl (colOn 2 4 x) w v))
        (ppAt 4 0 1 * mc 4 .box [0] (setCtl (colOn 1 4 x') w v) * ppAt 4 0 1) := by
    intro v
    cases v with
    | none => simpa only [drawn3] using hgPP_none4 ih x w hw hwN
    | some a =>
      have hk : 2 ≤ (ctrlWires 4 [0, 1] (setCtl (colOn 2 4 x) w (some a))).length := by
        apply hg_two 4 _ 2 3 (by decide) (by omega) (by omega) (by omega) (by omega) <;>
          simp only [setCtl] <;> split_ifs <;> simp [colOn]
      have h := hgPP 4 (by omega) _ hk
      rw [drawn3] at h
      refine h.trans (der_of_eq ?_)
      congr 2
      apply mc_congr
      intro i hi
      simp only [setCtl, colOn, x']
      split_ifs <;> first | rfl | omega
  rw [drawn2]
  refine (dmul (hv (some !b)) (hv (some b))).trans ?_
  have h := conj_prod (P := ppAt 4 0 1)
    (A := mc 4 .box [0] (setCtl (colOn 1 4 x') w (some b)))
    (B := mc 4 .box [0] (setCtl (colOn 1 4 x') w (some !b))) (pp_sq 4 (by omega) ih)
  rw [drawn2] at h
  refine h.trans ?_
  exact (dright _ (dleft _ (h309 x' w (by omega) hwN b))).trans (hv none).symm

end QCert.RealCliffordCH.Sec8.D.N8
