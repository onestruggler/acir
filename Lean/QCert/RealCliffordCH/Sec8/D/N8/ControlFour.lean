/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The four-wire cases of (290) and (291)

Expand the full ZX by Definition 2.4. Z on wire 1 passes the controlled
Hadamards and the conjugated boxes by (154); CZ on wires 1, 3 does so
by the relabelled equation (159).
-/
import QCert.RealCliffordCH.Sec8.D.N8.MoreLow

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

set_option maxRecDepth 100000

private def bx : WE.Tk := .g .box [0] [(3, true), (2, true), (1, true)]
private def zf : WE.Tk := .g .zx [0] [(3, true), (2, true), (1, true)]
private def k : WE.Tk := .s (.K 0)
private def s : WE.Tk := .s (.S 0)
private def z0 : WE.Tk := .s (.Z 0)
private def z1 : WE.Tk := .p 1 [.Z 0] [1]
private def zbox : WE.Tk := .g .box [0] [(1, true)]
private def c03 : WE.Tk := .p 2 [.C 0] [0, 3]
private def c13 : WE.Tk := .p 2 [.C 0] [1, 3]
private def cbox : WE.Tk := .g .box [0] [(3, true), (1, true)]

private theorem zf_expand :
    Derivable (theory 4) (WE.wcT 4 [zf]) (WE.wcT 4 [k, s, bx, s, k, s, bx, s]) := by
  exact der_of_eq (by rfl)

theorem eq290_4 (ih : IH 4) :
    Derivable (theory 4)
      (drawn [mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 4)),
        mc 4 .zx [0] (blackOn 1 4)])
      (drawn [mc 4 .zx [0] (blackOn 1 4),
        mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 4))]) := by
  have ht : WE.AllD 4
      [([zf], [k, s, bx, s, k, s, bx, s]), ([z0, bx], [bx, z0])] :=
    WE.AllD.cons zf_expand (WE.AllD.cons (W4.t154 ih) (WE.AllD.nil 4))
  exact WE.check_sound ih ht (w := [zbox, zf]) (v := [zf, zbox])
    (ss := [.sem 0 1 [z1] 2, .rw 1 0 false, .sem 0 2 [k, z1] 2,
      .sem 1 2 [s, z0] 2, .rw 2 1 false, .sem 3 2 [s, z1] 2,
      .sem 4 2 [k, z1] 2, .sem 5 2 [s, z0] 2, .rw 6 1 false,
      .sem 7 2 [s, z1] 2, .rw 0 0 true, .sem 1 1 [zbox] 2])
    (by decide +kernel)

theorem eq291_4 (ih : IH 4) :
    Derivable (theory 4)
      (drawn [mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 4)),
        mc 4 .zx [0] (blackOn 1 4)])
      (drawn [mc 4 .zx [0] (blackOn 1 4),
        mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 4))]) := by
  have hc : Derivable (theory 4) (WE.wcT 4 [c03, bx]) (WE.wcT 4 [bx, c03]) := by
    have h := WS.rel_entry (W4.havail4a ih) [2]
      (l' := [c03, .g .box [0] [(2, true), (3, true), (1, true)]])
      (r' := [.g .box [0] [(2, true), (3, true), (1, true)], c03])
      (by decide +kernel) (W4.t159 ih)
    exact h
  have ht : WE.AllD 4
      [([zf], [k, s, bx, s, k, s, bx, s]), ([c03, bx], [bx, c03])] :=
    WE.AllD.cons zf_expand (WE.AllD.cons hc (WE.AllD.nil 4))
  exact WE.check_sound ih ht (w := [cbox, zf]) (v := [zf, cbox])
    (ss := [.sem 0 1 [c13] 2, .rw 1 0 false, .sem 0 2 [k, c13] 2,
      .sem 1 2 [s, c03] 2, .rw 2 1 false, .sem 3 2 [s, c13] 2,
      .sem 4 2 [k, c13] 2, .sem 5 2 [s, c03] 2, .rw 6 1 false,
      .sem 7 2 [s, c13] 2, .rw 0 0 true, .sem 1 1 [cbox] 2])
    (by decide +kernel)

end QCert.RealCliffordCH.Sec8.D.N8
