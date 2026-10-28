/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Small-width instances for the Appendix D.8 interface

The four-wire merge equations are the checked runs (170a) and its colour
exchange. Their right-hand sides are placed CZ gates; a semantic step on
three wires identifies these with the boxes with one control removed.
-/
import QCert.RealCliffordCH.Sec8.D.N8.T3b
import QCert.RealCliffordCH.Sec8.D.W4.B2

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

set_option maxRecDepth 100000

theorem eq301_3 (ih : IH 3) :
    Derivable (theory 3)
      (drawn [BxI 3, mc 3 .box [0] (setCtl (blackOn 1 3) 2 (some false))])
      (mc 3 .box [0] (setCtl (blackOn 1 3) 2 none)) := by
  exact t301 ih

theorem eq302_3 (ih : IH 3) :
    Derivable (theory 3)
      (drawn [mc 3 .box [0] (setCtl (blackOn 1 3) 2 (some false)), BxI 3])
      (mc 3 .box [0] (setCtl (blackOn 1 3) 2 none)) := by
  exact t302 ih

private theorem merge_rhs4 (ih : IH 4) :
    Derivable (theory 4) (WE.wcT 4 W4.R170a)
      (mc 4 .box [0] (setCtl (blackOn 1 4) 2 none)) := by
  exact WE.check_sound ih (WE.AllD.nil 4)
    (w := W4.R170a) (v := [.g .box [0] [(1, true), (3, true)]])
    (ss := [.sem 0 1 [.g .box [0] [(1, true), (3, true)]] 2])
    (by decide +kernel)

theorem eq301_4 (ih : IH 4) :
    Derivable (theory 4)
      (drawn [BxI 4, mc 4 .box [0] (setCtl (blackOn 1 4) 2 (some false))])
      (mc 4 .box [0] (setCtl (blackOn 1 4) 2 none)) := by
  exact (W4.t170a ih).trans (merge_rhs4 ih)

theorem eq302_4 (ih : IH 4) :
    Derivable (theory 4)
      (drawn [mc 4 .box [0] (setCtl (blackOn 1 4) 2 (some false)), BxI 4])
      (mc 4 .box [0] (setCtl (blackOn 1 4) 2 none)) := by
  exact (W4.t170af2 ih).trans (merge_rhs4 ih)

theorem eq305_3 (ih : IH 3) :
    Derivable (theory 3)
      (drawn [mc 3 .xz [0] (ctlAt 1 true),
        mc 3 .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 3)),
        mc 3 .zx [0] (ctlAt 1 true),
        mc 3 .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 3))]) (BxI 3) := by
  exact t305 ih

private def b4 : WE.Tk := .g .box [0] [(1, true), (2, true), (3, true)]
private def c4 : WE.Tk := .g .box [1] [(0, true), (3, true)]
private def w4 : WE.Tk := .g .zx [0] [(1, true), (2, true)]
private def v4 : WE.Tk := .g .xz [0] [(1, true), (2, true)]

theorem eq300_4 (ih : IH 4) :
    Derivable (theory 4) (BxI 4)
      (drawn [Bx1I 4, mc 4 .zx [0] (blackOn 1 3), Bx1I 4,
        mc 4 .xz [0] (blackOn 1 3)]) := by
  have ht : WE.AllD 4 [([b4], [w4, c4, v4, c4]), ([b4, b4], [])] :=
    WE.AllD.cons (eq269_ge4 0) (WE.AllD.cons (W4.t166 ih) (WE.AllD.nil 4))
  exact WE.check_sound ih ht (w := [b4]) (v := [c4, w4, c4, v4])
    (ss := [.sem 0 0 [c4, c4] 2, .sem 1 0 [w4, v4] 3,
      .sem 2 0 [c4, c4] 2, .sem 3 0 [v4, w4] 3,
      .rw 4 0 true, .rw 4 1 false]) (by decide +kernel)

theorem eq312_3 (ih : IH 3) (x : ℕ → Bool) :
    Derivable (theory 3)
      (drawn [mc 3 .hg [0, 1] (colOn 2 3 x), mc 3 .hg [0, 1] (colOn 2 3 x)]) 1 := by
  have hG : mc 3 .hg [0, 1] (colOn 2 3 x) =
      (if x 2 then hg3T else hg3F).circ 3 3 := by
    cases hx : x 2 <;> apply mc_congr <;> intro i hi <;>
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      simp [colOn, ctl, hx] <;> rfl
  rw [hG]
  cases hx : x 2
  · exact t312 ih false
  · exact t312 ih true

end QCert.RealCliffordCH.Sec8.D.N8
