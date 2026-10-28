/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The small-width cases of (292) and (305)

Inverting the three-wire ZX gadget transfers (176) to (292). For (305),
the two orientations of ZX differ by Z on its control; this Z commutes
with the box by the relabelled equation (154).
-/
import QCert.RealCliffordCH.Sec8.D.N8.Low

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

set_option maxRecDepth 100000

theorem eq292_3 (ih : IH 3) :
    Derivable (theory 3)
      (drawn [mc 3 .zx [0] (blackOn 1 3),
        mc 3 .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 3)))])
      (drawn [mc 3 .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 3))),
        mc 3 .zx [0] (blackOn 1 3)]) := by
  exact t292 ih

private def Z4 : WE.Tk := .g .zx [0] [(2, true), (1, true)]
private def V4 : WE.Tk := .g .xz [0] [(2, true), (1, true)]
private def B4 : WE.Tk := .g .box [1] [(3, true), (2, false), (0, true)]

theorem eq292_4 (ih : IH 4) :
    Derivable (theory 4)
      (drawn [mc 4 .zx [0] (blackOn 1 3),
        mc 4 .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 4)))])
      (drawn [mc 4 .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 4))),
        mc 4 .zx [0] (blackOn 1 3)]) := by
  have ht : WE.AllD 4 [([V4, B4], [B4, V4])] :=
    WE.AllD.cons (W4.t176f2 ih) (WE.AllD.nil 4)
  exact WE.check_sound ih ht (w := [Z4, B4]) (v := [B4, Z4])
    (ss := [.sem 2 0 [V4, Z4] 3, .rw 1 0 true, .sem 0 2 [] 3])
    (by decide +kernel)

private def w1 : WE.Tk := .g .zx [0] [(1, true)]
private def v1 : WE.Tk := .g .xz [0] [(1, true)]
private def z1 : WE.Tk := .p 1 [.Z 0] [1]
private def bp : WE.Tk := .g .box [1] [(3, true), (2, true), (0, true)]
private def bx : WE.Tk := .g .box [0] [(3, true), (2, true), (1, true)]

theorem eq305_4 (ih : IH 4) :
    Derivable (theory 4)
      (drawn [mc 4 .xz [0] (ctlAt 1 true),
        mc 4 .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)),
        mc 4 .zx [0] (ctlAt 1 true),
        mc 4 .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 4))]) (BxI 4) := by
  have hz : Derivable (theory 4) (WE.wcT 4 [z1, bp]) (WE.wcT 4 [bp, z1]) :=
    WS.rel_entry (W4.havail4a ih) [0] (by decide +kernel) (W4.t154 ih)
  have ht : WE.AllD 4 [([z1, bp], [bp, z1]), ([bx], [w1, bp, v1, bp])] :=
    WE.AllD.cons hz (WE.AllD.cons (W4.t178 ih) (WE.AllD.nil 4))
  exact WE.check_sound ih ht (w := [v1, bp, w1, bp]) (v := [bx])
    (ss := [.sem 0 1 [w1, z1] 2, .rw 1 0 false,
      .sem 2 2 [v1] 2, .rw 0 1 true]) (by decide +kernel)

end QCert.RealCliffordCH.Sec8.D.N8
