/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.8–D.9 (Lemmas D.14–D.15) and Equation (361): package (vi)

The equations of Lemmas D.14 and D.15 and the auxiliary Equation (361) of
Appendix E.5 (the decoding of `X_[0,3]X_[1,2]`), stated on `N` wires with
completeness on fewer wires as a hypothesis (`IH N`, Lemma 5.1), in the
conventions of `MC` (see `PLAN.md`).  The sign `(-1)ᵃ` of a `ZX` label is a
Boolean `a` (`Kind.sgnZX a`: `ZX` for `false`, `XZ` for `true`); `Λˣ`, `Λʸ`
are colourings of the wires around the distinguished one (`colOn 1 N x`
with the distinguished wire `w` set by `setCtl`); the single-qubit `ZX` and
`XZ` gates of (359) are `zx 0`, `xz 0` placed on their wire.

Transcribed from renders of the figures at 400 dpi, and checked numerically
against the definitions at `N = 2, …, 6` for every colouring
(`gen/sec8/e/iface_n15.py`; (361) at `N = 3, 4, 5`).
-/
import QCert.RealCliffordCH.Sec8.D.N13
import QCert.RealCliffordCH.Sec8.D.N15.E359

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

/-- The single-qubit `ZX` gate (`X`, then `Z`) on wire `j`. -/
def zxAt (N j : ℕ) : Circ N := placeG N (zx 0) [j]

/-- The single-qubit `XZ` gate (`Z`, then `X`) on wire `j`. -/
def xzAt (N j : ℕ) : Circ N := placeG N (xz 0) [j]

/-! ## Lemma D.14 -/

/-- (353): the multi-controlled `(-1)ᵃ ZX` commutes with the swap of two of
its controls. -/
theorem eq353 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (a : Bool) (j : ℕ) (hj : 1 ≤ j)
    (hjN : j + 2 ≤ N) :
    Derivable (theory N) (drawn [mc N (Kind.sgnZX a) [0] (blackOn 1 N), swAt N j])
      (drawn [swAt N j, mc N (Kind.sgnZX a) [0] (blackOn 1 N)]) := by
  exact N15.eq353 N hN ih a j hj hjN

/-- (354): a black and a white control of a multi-controlled `(-1)ᵃ ZX` on the
same wire `w` merge (in either order, `b` the colour of the first). -/
theorem eq354 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (a : Bool) (x : ℕ → Bool) (w : ℕ) (hw : 1 ≤ w)
    (hwN : w < N) (b : Bool) :
    Derivable (theory N)
      (drawn [mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some b)),
        mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some !b))])
      (mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w none)) := by
  exact N15.eq354 N hN ih a x w hw hwN b

/-! ## Lemma D.15 -/

/-- (355): the square of a multi-controlled `(-1)ᵃ XZ` is the box with the
same controls. -/
theorem eq355 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (a : Bool) (x : ℕ → Bool) :
    Derivable (theory N)
      (drawn [mc N (Kind.sgnZX a) [0] (colOn 1 N x), mc N (Kind.sgnZX a) [0] (colOn 1 N x)])
      (mc N .box [0] (colOn 1 N x)) := by
  exact N15.eq355 N hN ih a x

/-- (356): `X` on the target on both sides turns `ZX` into `XZ`. -/
theorem eq356 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, mc N .zx [0] (blackOn 1 N), xAt N 0])
      (mc N .xz [0] (blackOn 1 N)) := by
  exact N15.eq356 N hN ih

/-- (357): the `CZ` of the target and the control on wire `1`, on both sides,
turns `ZX` into `XZ`. -/
theorem eq357 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [czAt N 0 1, mc N .zx [0] (blackOn 1 N), czAt N 0 1])
      (mc N .xz [0] (blackOn 1 N)) := by
  exact N15.eq357 N hN ih

/-- (358): the braid relation of the multi-controlled `XZ` on wire `0` and the
multi-controlled `ZX` on wire `1`, each controlled by the other's target and
by the wires above. -/
theorem eq358 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [mc N .xz [0] (blackOn 1 N), mc N .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .xz [0] (blackOn 1 N)])
      (drawn [mc N .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)), mc N .xz [0] (blackOn 1 N),
        mc N .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))]) := by
  sorry

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
  exact N15.eq359 N hN ih a x w hw hwN α

/-- (360): `P ⊗ P` on the target (wire `1`) and the idle wire `0` turns `ZX`
into `XZ`. -/
theorem eq360 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [ppAt N 0 1, mc N .zx [1] (blackOn 2 N)])
      (drawn [mc N .xz [1] (blackOn 2 N), ppAt N 0 1]) := by
  sorry

/-! ## Equation (361) (Appendix E.5, decoding Equation (43)) -/

/-- (361): the decoding of `X_[0,3]X_[1,2]` is the box on wire `0` controlled
by wire `1` (black) and the wires above (white), followed by the `XZ` on
wire `1` controlled by the wires above (white). -/
theorem eq361 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (decW N (wordOf [Xx N 0 3 1 2]))
      (drawn [mc N .box [0] (ctlOr (ctlAt 1 true) (colOn 2 N fun _ => false)),
        mc N .xz [1] (colOn 2 N fun _ => false)]) := by
  sorry

end QCert.RealCliffordCH.Sec8.D
