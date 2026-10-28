/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (336) with equal colourings, all black

The box on wire `0` and the box on wire `1`, every other wire a black
control, commute.  The paper's chain on five local wires: by (269) the
first box is `W C V C` (`C` the box on wire `1` without control on wire
`2`), `C` is the second box times its version white on wire `2`
((309), (302)), which passes `V` by (292) and cancels ((311), (299)); so
both products are `W B V`, the second by (300).  The equations on the box
with box wire `1` come from those on the box with box wire `0` by the swap
of the wires `0, 1` (`swapE`).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E319

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## The letters -/

/-- The box on wire `0` white on wire `2`. -/
def bx0w : Lt := .g .box [0] [(1, true), (2, false), (3, true), (4, true)] true
/-- The box on wire `1`, all other wires black. -/
def bxB : Lt := .g .box [1] [(0, true), (2, true), (3, true), (4, true)] true
/-- The box on wire `1` white on wire `2`. -/
def bxBw : Lt := .g .box [1] [(0, true), (2, false), (3, true), (4, true)] true

/-! ## Merges and involutions on the box wire `0` -/

theorem t309 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0, bx0w]) (wc 5 (m + 5) [E1']) := by
  have h := eq309 (m + 5) (by omega) ih (fun _ => true) 2 (by omega) (by omega) true
  have e1 : bx0.circ 5 (m + 5) =
      mc (m + 5) .box [0] (setCtl (colOn 1 (m + 5) (fun _ => true)) 2 (some true)) :=
    mc_congr _ _ _ (by ctl_tac)
  have e2 : bx0w.circ 5 (m + 5) =
      mc (m + 5) .box [0] (setCtl (colOn 1 (m + 5) (fun _ => true)) 2 (some !true)) :=
    mc_congr _ _ _ (by ctl_tac)
  have e3 : E1'.circ 5 (m + 5) =
      mc (m + 5) .box [0] (setCtl (colOn 1 (m + 5) (fun _ => true)) 2 none) :=
    mc_congr _ _ _ (by ctl_tac)
  rw [wc_two, wc_one', e1, e2, e3]
  exact h

theorem t302 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0w, bx0]) (wc 5 (m + 5) [E1']) := by
  have h := eq302 (m + 5) (by omega) ih
  have e1 : bx0.circ 5 (m + 5) = Bx (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e2 : bx0w.circ 5 (m + 5) =
      mc (m + 5) .box [0] (setCtl (blackOn 1 (m + 5)) 2 (some false)) :=
    mc_congr _ _ _ (by ctl_tac)
  have e3 : E1'.circ 5 (m + 5) = mc (m + 5) .box [0] (setCtl (blackOn 1 (m + 5)) 2 none) :=
    mc_congr _ _ _ (by ctl_tac)
  rw [wc_two, wc_one', e1, e2, e3]
  exact h

theorem t311w (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0w, bx0w]) (wc 5 (m + 5) []) := by
  have h := eq311 (m + 5) (by omega) ih (fun j => j != 2)
  have e : bx0w.circ 5 (m + 5) = mc (m + 5) .box [0] (colOn 1 (m + 5) (fun j => j != 2)) :=
    mc_congr _ _ _ (by ctl_tac)
  rw [wc_two, e]
  exact h

theorem t299 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0, bx0]) (wc 5 (m + 5) []) := by
  have h := eq299 (m + 5) (by omega) ih
  have e : bx0.circ 5 (m + 5) = Bx (m + 5) := mc_congr _ _ _ (by ctl_tac)
  rw [wc_two, e]
  exact h

/-! ## On the box wire `1` -/

def Tsw : SE.Tbl :=
  [([bx0, bx0w], [E1']), ([bx0w, bx0], [E1']), ([bx0w, bx0w], []), ([bx0, bx0], []),
   ([.s (.S 0), bx0, .s (.S 0)], [bxB]), ([.s (.S 0), bx0w, .s (.S 0)], [bxBw]),
   ([.s (.S 0), E1', .s (.S 0)], [cC])]

theorem Tsw_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m Tsw := by
  intro e he
  simp only [Tsw, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact t309 m ih
  · exact t302 m ih
  · exact t311w m ih
  · exact t299 m ih
  · exact swapE m 5 0 (by omega) .box [0] _ true (by decide) (by decide)
  · exact swapE m 5 0 (by omega) .box [0] _ true (by decide) (by decide)
  · exact swapE m 5 0 (by omega) .box [0] _ true (by decide) (by decide)

/-- Conjugating a two-letter rule by the swap of the wires `0, 1`. -/
def conjSteps (a b c : ℕ) (r : ℕ) (rhs1 : Bool) : List St :=
  [.rw 0 a true, .rw 3 b true, .sem 2 2 [] 2, .rw 1 r false] ++
    (if rhs1 then [.rw 0 c false] else [.sem 0 2 [] 2])

theorem chkSw : check 4 Tsw [bxB, bxBw] [cC] (conjSteps 4 5 6 0 true) = true ∧
    check 4 Tsw [bxBw, bxB] [cC] (conjSteps 5 4 6 1 true) = true ∧
    check 4 Tsw [bxBw, bxBw] [] (conjSteps 5 5 6 2 false) = true ∧
    check 4 Tsw [bxB, bxB] [] (conjSteps 4 4 6 3 false) = true := by
  decide +kernel

/-! ## The chain -/

def T336 : SE.Tbl :=
  [([bx0], [wW, cC, wV, cC]), ([bxB, bxBw], [cC]), ([bxBw, bxB], [cC]), ([wW, bxBw], [bxBw, wW]),
   ([bxBw, bxBw], []), ([bxB, bxB], []), ([bx0], [cC, wW, cC, wV])]

theorem t292 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [wW, bxBw]) (wc 5 (m + 5) [bxBw, wW]) := by
  have h := eq292 (m + 5) (by omega) ih
  have e1 : wW.circ 5 (m + 5) = mc (m + 5) .zx [0] (blackOn 1 3) := mc_congr _ _ _ (by ctl_tac)
  have e2 : bxBw.circ 5 (m + 5) =
      mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 (m + 5)))) :=
    mc_congr _ _ _ (by ctl_tac)
  rw [wc_two, wc_two, e1, e2]
  exact h

theorem t300 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0]) (wc 5 (m + 5) [cC, wW, cC, wV]) := by
  have h := eq300 (m + 5) (by omega) ih
  have e0 : bx0.circ 5 (m + 5) = Bx (m + 5) := mc_congr _ _ _ (by ctl_tac)
  have e1 : wW.circ 5 (m + 5) = mc (m + 5) .zx [0] (blackOn 1 3) := mc_congr _ _ _ (by ctl_tac)
  have e2 : wV.circ 5 (m + 5) = mc (m + 5) .xz [0] (blackOn 1 3) := mc_congr _ _ _ (by ctl_tac)
  have e3 : cC.circ 5 (m + 5) = Bx1 (m + 5) := mc_congr _ _ _ (by ctl_tac)
  rw [wc_one', e0]
  simp only [wc, List.map_cons, List.map_nil, e1, e2, e3]
  exact h

theorem T336_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T336 := by
  intro e he
  simp only [T336, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact t269 m
  · exact check_sound (frame 4) ih (Tsw_ok m ih) chkSw.1
  · exact check_sound (frame 4) ih (Tsw_ok m ih) chkSw.2.1
  · exact t292 m ih
  · exact check_sound (frame 4) ih (Tsw_ok m ih) chkSw.2.2.1
  · exact check_sound (frame 4) ih (Tsw_ok m ih) chkSw.2.2.2
  · exact t300 m ih

/-- From `[B_A, B_B]` to `W B_B V`, then back to `[B_B, B_A]`. -/
def run336 : List St :=
  [.rw 0 0 false, .rw 1 1 true, .rw 4 2 true, .sem 2 0 [wV, wW] 3, .rw 3 3 false, .sem 4 2 [] 3,
   .rw 3 4 false, .rw 3 5 false,
   .rw 1 4 true, .rw 2 2 false, .rw 0 3 false, .rw 0 5 true, .rw 1 1 false, .rw 1 6 true]

theorem chk336 : check 4 T336 [bx0, bxB] [bxB, bx0] run336 = true := by
  decide +kernel

theorem r336 (m : ℕ) (ih : IH (m + 5)) :
    Comm (m + 5) (bx0.circ 5 (m + 5)) (bxB.circ 5 (m + 5)) :=
  check_sound (frame 4) ih (T336_ok m ih) chk336

end QCert.RealCliffordCH.Sec8.D.N13
