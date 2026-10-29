/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (295) on four wires

The paper's proof of (295)ₙ at `n = 4`.  From five wires on (`IFive`), the
steps on all four lower wires are semantic steps with the fifth wire idle;
here they are the equations of Appendix D.3 at width four instead:

* the inner box `C` of (269) (box wire `1`, controls `0`, `3`) passes the `ZX`
  on wire `1` controlled by `0, 2, 3` ((291) under the swap of the wires `0, 1`),
  hence the `XZ` (the inverse pairs (208) under the same swap), hence the `ZX`
  white on wire `2` (`(226)`, the black one times the one without a control
  on wire `2`);
* (293) on four wires, the paper's proof: (269), (216), the previous item,
  (217);
* the second line of the paper's proof of (295): the box conjugated by the
  white `ZX` ((209), (293)), (269), `C` written by (269) one width down
  (Lemma 5.1), (218), (225), (226), and (221), (222), (217), (209);
* the colours on wire `3`: (223), (240) under the swaps of the wires `0, 1`
  and `2, 3` (the control symmetries of `ZX` and `XZ` from (214), (215),
  `W4.havail4b`), (290) under `X` on wire `3` ((81)), (224) and (208).

Every run was checked numerically first (scratch `p295.py`, the model
`gen/sec8/w4/tok.py` of `WEng`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.ControlFour
import QCert.RealCliffordCH.Sec8.D.N8.I269
import QCert.RealCliffordCH.Sec8.D.W4.AvailFull
import QCert.RealCliffordCH.Sec8.D.W4.FullRotation
import QCert.RealCliffordCH.Sec8.D.W4.SameRotation
import QCert.RealCliffordCH.Sec8.D.W4.Opposite
import QCert.RealCliffordCH.Sec8.D.W4.MergeZX

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

set_option maxRecDepth 100000

namespace F295

/-! ## Tokens -/

/-- The box on wire `0`, controls `1, 2, 3`. -/
def bx0 : WE.Tk := .g .box [0] [(3, true), (2, true), (1, true)]
/-- `W`, `V`: the `ZX`, `XZ` on wire `0` controlled by `1, 2`. -/
def wW : WE.Tk := .g .zx [0] [(2, true), (1, true)]
def wV : WE.Tk := .g .xz [0] [(2, true), (1, true)]
/-- `C`: the box on wire `1`, controls `0, 3`. -/
def cC : WE.Tk := .g .box [1] [(3, true), (0, true)]
/-- The `ZX`, `XZ` on wire `1` controlled by `0, 3`, white on `2`. -/
def Abz : WE.Tk := .g .zx [1] [(3, true), (2, false), (0, true)]
def Abx : WE.Tk := .g .xz [1] [(3, true), (2, false), (0, true)]
/-- The `ZX`, `XZ` on wire `1` controlled by `0, 2, 3`. -/
def A2z : WE.Tk := .g .zx [1] [(3, true), (2, true), (0, true)]
def A2x : WE.Tk := .g .xz [1] [(3, true), (2, true), (0, true)]
/-- The `ZX`, `XZ` on wire `1` controlled by `0, 3`. -/
def A1z : WE.Tk := .g .zx [1] [(3, true), (0, true)]
def A1x : WE.Tk := .g .xz [1] [(3, true), (0, true)]
/-- The box on wire `0` with the one control `1`. -/
def D4 : WE.Tk := .g .box [0] [(1, true)]
/-- The `ZX`, `XZ` on wire `0` controlled by `1, 2, 3`. -/
def Z123 : WE.Tk := .g .zx [0] [(3, true), (2, true), (1, true)]
def X123 : WE.Tk := .g .xz [0] [(3, true), (2, true), (1, true)]
/-- The same, white on wire `3`. -/
def Zw : WE.Tk := .g .zx [0] [(3, false), (2, true), (1, true)]
def Xw : WE.Tk := .g .xz [0] [(3, false), (2, true), (1, true)]
/-- The box on wire `0`, controls `1, 3`. -/
def B31 : WE.Tk := .g .box [0] [(3, true), (1, true)]
/-- `X` on wire `3`. -/
def x3 : WE.Tk := WS.xT 3
/-- `A2z`, `A2x`, `Zw` with their controls listed as (240) relabelled lists them. -/
def A2z' : WE.Tk := .g .zx [1] [(2, true), (3, true), (0, true)]
def A2x' : WE.Tk := .g .xz [1] [(2, true), (3, true), (0, true)]
def Zw' : WE.Tk := .g .zx [0] [(2, true), (3, false), (1, true)]

theorem one_eq (x : WE.Tk) : WE.wcT 4 [x] = x.circ 4 := by simp [WE.wcT, drawn]

/-! ## Equations read off the interface statements -/

theorem e269t : Derivable (theory 4) (WE.wcT 4 [bx0]) (WE.wcT 4 [wW, cC, wV, cC]) := by
  have h := eq269_ge4 0
  have e1 : WE.wcT 4 [bx0] = BxI 4 := by
    rw [one_eq]; exact mc_congr _ _ _ (by decide)
  have a : wW.circ 4 = mc 4 .zx [0] (blackOn 1 3) := mc_congr _ _ _ (by decide)
  have b : cC.circ 4 = Bx1I 4 := mc_congr _ _ _ (by decide)
  have c : wV.circ 4 = mc 4 .xz [0] (blackOn 1 3) := mc_congr _ _ _ (by decide)
  have e2 : WE.wcT 4 [wW, cC, wV, cC] =
      drawn [mc 4 .zx [0] (blackOn 1 3), Bx1I 4, mc 4 .xz [0] (blackOn 1 3), Bx1I 4] := by
    show drawn [wW.circ 4, cC.circ 4, wV.circ 4, cC.circ 4] = _
    rw [a, b, c]
  rw [e1, e2]; exact h

theorem e291t (ih : IH 4) :
    Derivable (theory 4) (WE.wcT 4 [B31, Z123]) (WE.wcT 4 [Z123, B31]) := by
  have h := eq291_4 ih
  have a : B31.circ 4 = mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 4)) :=
    mc_congr _ _ _ (by decide)
  have b : Z123.circ 4 = mc 4 .zx [0] (blackOn 1 4) := mc_congr _ _ _ (by decide)
  have e1 : WE.wcT 4 [B31, Z123] = drawn [mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 4)),
      mc 4 .zx [0] (blackOn 1 4)] := by
    show drawn [B31.circ 4, Z123.circ 4] = _
    rw [a, b]
  have e2 : WE.wcT 4 [Z123, B31] = drawn [mc 4 .zx [0] (blackOn 1 4),
      mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 4))] := by
    show drawn [Z123.circ 4, B31.circ 4] = _
    rw [a, b]
  rw [e1, e2]; exact h

theorem e290t (ih : IH 4) :
    Derivable (theory 4) (WE.wcT 4 [D4, Z123]) (WE.wcT 4 [Z123, D4]) := by
  have h := eq290_4 ih
  have a : D4.circ 4 = mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 4)) :=
    mc_congr _ _ _ (by decide)
  have b : Z123.circ 4 = mc 4 .zx [0] (blackOn 1 4) := mc_congr _ _ _ (by decide)
  have e1 : WE.wcT 4 [D4, Z123] = drawn [mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 4)),
      mc 4 .zx [0] (blackOn 1 4)] := by
    show drawn [D4.circ 4, Z123.circ 4] = _
    rw [a, b]
  have e2 : WE.wcT 4 [Z123, D4] = drawn [mc 4 .zx [0] (blackOn 1 4),
      mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 4))] := by
    show drawn [Z123.circ 4, D4.circ 4] = _
    rw [a, b]
  rw [e1, e2]; exact h

/-! ## Relabelled equations of D.3 -/

/-- (291) under the swap of the wires `0, 1`: `C` passes `A2z`. -/
theorem e291c (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [cC, A2z]) (WE.wcT 4 [A2z, cC]) :=
  WS.rel_entry (W4.havail4b ih) [0] (l := [B31, Z123]) (r := [Z123, B31]) (by decide +kernel)
    (e291t ih)

/-- The inverse pairs on wire `1`, (208) under the swap of the wires `0, 1`. -/
theorem e208a (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [A2z, A2x]) (WE.wcT 4 []) :=
  WS.rel_entry (W4.havail4b ih) [0] (l := W4.L208f0) (r := W4.R208f0) (by decide +kernel)
    (W4.t208f0 ih)

theorem e208b (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [A2x, A2z]) (WE.wcT 4 []) :=
  WS.rel_entry (W4.havail4b ih) [0] (l := W4.L208) (r := W4.R208) (by decide +kernel)
    (W4.t208 ih)

/-- (240) under the swaps of the wires `0, 1` and `2, 3`. -/
theorem e240a' (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [A2z', Zw']) (WE.wcT 4 [Zw', A2z']) :=
  WS.rel_entry (W4.havail4b ih) [0, 2] (l := W4.L240TTTTTT) (r := W4.R240TTTTTT)
    (by decide +kernel) (W4.t240TTTTTT ih)

theorem e240b' (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [A2x', Zw']) (WE.wcT 4 [Zw', A2x']) :=
  WS.rel_entry (W4.havail4b ih) [0, 2] (l := W4.L240FTTTTT) (r := W4.R240FTTTTT)
    (by decide +kernel) (W4.t240FTTTTT ih)

/-- (81): `X` on wire `3` around `Z123` is `Zw`. -/
theorem eX3 : Derivable (theory 4) (WE.wcT 4 [x3, Z123, x3]) (WE.wcT 4 [Zw]) :=
  WS.x81_entry 3 .zx [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)]
    (by decide +kernel)

/-! ## Runs -/

/-- `C` passes `A2x`. -/
theorem e291cx (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [cC, A2x]) (WE.wcT 4 [A2x, cC]) :=
  WE.check_sound ih
    (WE.AllD.cons (e291c ih) (WE.AllD.cons (e208a ih) (WE.AllD.cons (e208b ih) (WE.AllD.nil 4))))
    (w := [cC, A2x]) (v := [A2x, cC])
    (ss := [.rw 0 2 true, .rw 1 0 true, .rw 2 1 false]) (by decide +kernel)

/-- `C` passes the `ZX` white on wire `2`. -/
theorem eAbC (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [Abz, cC]) (WE.wcT 4 [cC, Abz]) :=
  WE.check_sound ih
    (WE.AllD.cons (W4.t226 ih) (WE.AllD.cons (e291cx ih) (WE.AllD.nil 4)))
    (w := [Abz, cC]) (v := [cC, Abz])
    (ss := [.sem 0 0 [A1z, A1x] 2, .rw 1 0 false, .rw 1 1 true, .sem 0 2 [cC, A1z] 2,
      .rw 2 0 true, .sem 1 2 [] 2]) (by decide +kernel)

/-- (293) on four wires: the `ZX` on wire `1` white on wire `2` passes the box. -/
theorem e293 (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [Abz, bx0]) (WE.wcT 4 [bx0, Abz]) :=
  WE.check_sound ih
    (WE.AllD.cons e269t (WE.AllD.cons (W4.t216 ih) (WE.AllD.cons (eAbC ih)
      (WE.AllD.cons (W4.t217 ih) (WE.AllD.nil 4)))))
    (w := [Abz, bx0]) (v := [bx0, Abz])
    (ss := [.rw 1 0 false, .rw 0 1 false, .rw 1 2 false, .rw 2 3 false, .rw 3 2 false,
      .rw 0 0 true]) (by decide +kernel)

/-- The factors of the second line of the paper's proof of (295). -/
def Fline2 : List WE.Tk := [wW, A2z, D4, A2x, wV, A2z, D4, A2x]

/-- The second line of the paper's proof of (295), on four wires. -/
theorem e295a (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [bx0]) (WE.wcT 4 Fline2) :=
  WE.check_sound ih
    (WE.AllD.cons (W4.t209 ih) (WE.AllD.cons (e293 ih) (WE.AllD.cons e269t
      (WE.AllD.cons (W4.t218 ih) (WE.AllD.cons (W4.t225 ih) (WE.AllD.cons (W4.t226 ih)
      (WE.AllD.cons (W4.t221 ih) (WE.AllD.cons (W4.t222 ih) (WE.AllD.cons (W4.t217 ih)
      (WE.AllD.nil 4))))))))))
    (w := [bx0]) (v := Fline2)
    (ss := [.rw 0 0 true, .rw 1 1 false, .rw 1 2 false,
      .sem 2 1 [A1z, D4, A1x, D4] 2, .sem 7 1 [A1z, D4, A1x, D4] 2, .sem 5 2 [wV, D4] 3,
      .sem 6 5 [A1z, D4, A1x] 2, .rw 0 3 false, .rw 1 4 false, .rw 7 5 false,
      .rw 3 7 true, .rw 6 6 true, .rw 5 8 true, .rw 4 0 false]) (by decide +kernel)

/-- (290) white on wire `3`. -/
theorem e290w (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [D4, Zw]) (WE.wcT 4 [Zw, D4]) :=
  WE.check_sound ih (WE.AllD.cons (e290t ih) (WE.AllD.cons eX3 (WE.AllD.nil 4)))
    (w := [D4, Zw]) (v := [Zw, D4])
    (ss := [.rw 1 1 true, .sem 0 2 [x3, D4] 2, .rw 1 0 false, .sem 2 2 [x3, D4] 2,
      .rw 0 1 false]) (by decide +kernel)

theorem gA2z : Derivable (theory 4) (WE.wcT 4 [A2z]) (WE.wcT 4 [A2z']) :=
  WS.g_entry .zx [1] [(3, true), (2, true), (0, true)] [(2, true), (3, true), (0, true)]
    (by decide +kernel)

theorem gA2x : Derivable (theory 4) (WE.wcT 4 [A2x]) (WE.wcT 4 [A2x']) :=
  WS.g_entry .xz [1] [(3, true), (2, true), (0, true)] [(2, true), (3, true), (0, true)]
    (by decide +kernel)

theorem gZw : Derivable (theory 4) (WE.wcT 4 [Zw]) (WE.wcT 4 [Zw']) :=
  WS.g_entry .zx [0] [(3, false), (2, true), (1, true)] [(2, true), (3, false), (1, true)]
    (by decide +kernel)

/-- `A2z` passes the `ZX` white on wire `3`. -/
theorem e240a (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [A2z, Zw]) (WE.wcT 4 [Zw, A2z]) :=
  WE.check_sound ih
    (WE.AllD.cons (e240a' ih) (WE.AllD.cons gA2z (WE.AllD.cons gZw (WE.AllD.nil 4))))
    (w := [A2z, Zw]) (v := [Zw, A2z])
    (ss := [.rw 0 1 false, .rw 1 2 false, .rw 0 0 false, .rw 0 2 true, .rw 1 1 true])
    (by decide +kernel)

/-- `A2x` passes the `ZX` white on wire `3`. -/
theorem e240b (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [A2x, Zw]) (WE.wcT 4 [Zw, A2x]) :=
  WE.check_sound ih
    (WE.AllD.cons (e240b' ih) (WE.AllD.cons gA2x (WE.AllD.cons gZw (WE.AllD.nil 4))))
    (w := [A2x, Zw]) (v := [Zw, A2x])
    (ss := [.rw 0 1 false, .rw 1 2 false, .rw 0 0 false, .rw 0 2 true, .rw 1 1 true])
    (by decide +kernel)

/-- The factors of (295) as in the interface. -/
def F295i : List WE.Tk := [Z123, A2z, D4, A2x, X123, A2z, D4, A2x]

/-- (295) on four wires, in tokens. -/
theorem e295 (ih : IH 4) : Derivable (theory 4) (WE.wcT 4 [bx0]) (WE.wcT 4 F295i) :=
  WE.check_sound ih
    (WE.AllD.cons (e295a ih) (WE.AllD.cons (W4.t223 ih) (WE.AllD.cons (e240a ih)
      (WE.AllD.cons (e290w ih) (WE.AllD.cons (e240b ih) (WE.AllD.cons (W4.t224 ih)
      (WE.AllD.cons (W4.t208f0f3 ih) (WE.AllD.nil 4))))))))
    (w := [bx0]) (v := F295i)
    (ss := [.rw 0 0 false, .rw 0 1 true, .rw 1 2 true, .rw 2 3 true, .rw 3 4 true,
      .rw 5 5 true, .rw 4 6 false]) (by decide +kernel)

end F295

/-- (295) on four wires, in the conventions of the interface. -/
theorem eq295_4 (ih : IH 4) :
    Derivable (theory 4) (BxI 4)
      (drawn [mc 4 .zx [0] (blackOn 1 4), mc 4 .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)),
        mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 4)),
        mc 4 .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)), mc 4 .xz [0] (blackOn 1 4),
        mc 4 .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)),
        mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 4)),
        mc 4 .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4))]) := by
  have h := F295.e295 ih
  have e1 : WE.wcT 4 [F295.bx0] = BxI 4 := by
    rw [F295.one_eq]; exact mc_congr _ _ _ (by decide)
  have a : F295.Z123.circ 4 = mc 4 .zx [0] (blackOn 1 4) := mc_congr _ _ _ (by decide)
  have b : F295.A2z.circ 4 = mc 4 .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)) :=
    mc_congr _ _ _ (by decide)
  have c : F295.D4.circ 4 = mc 4 .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 4)) :=
    mc_congr _ _ _ (by decide)
  have d : F295.A2x.circ 4 = mc 4 .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)) :=
    mc_congr _ _ _ (by decide)
  have e : F295.X123.circ 4 = mc 4 .xz [0] (blackOn 1 4) := mc_congr _ _ _ (by decide)
  have e2 : WE.wcT 4 F295.F295i = drawn [F295.Z123.circ 4, F295.A2z.circ 4, F295.D4.circ 4,
      F295.A2x.circ 4, F295.X123.circ 4, F295.A2z.circ 4, F295.D4.circ 4, F295.A2x.circ 4] := rfl
  rw [e1, e2, a, b, c, d, e] at h
  exact h

end QCert.RealCliffordCH.Sec8.D.N8
