/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.5–D.6 (Lemmas D.8–D.11): the interface of package (iv)

The equations of Lemmas D.8–D.11 that later packages use, stated on `N`
wires with completeness on fewer wires as a hypothesis (`IH N`, Lemma 5.1),
in the conventions of `MC` (see `PLAN.md`): `mc N K tg c` is the
multi-controlled gate of kind `K` with special wires `tg` (box wire; target;
box wire then `H` wire) and controls `c`.  Every statement here was checked
numerically against the definitions at `N = 3, …, 6` (scratch
`r87/iface.py`).  They are stated, not yet proved: package (iv) of
`PLAN.md` replaces each `sorry` by its proof and keeps the statements.
-/
import QCert.RealCliffordCH.Sec8.MC

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

/-- The box on wire `0` with black controls on every other wire. -/
abbrev Bx (N : ℕ) : Circ N := mc N .box [0] (blackOn 1 N)

/-- (81), for every multi-controlled gate: `X` on a control wire on both
sides exchanges the colour of that control. -/
theorem eq81 (N : ℕ) (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool) (j : ℕ) (b : Bool)
    (hj : j < N) (hjt : j ∉ tg) (hc : c j = some b) :
    Derivable (theory N) (drawn [xAt N j, mc N K tg c, xAt N j])
      (mc N K tg (setCtl c j (some !b))) := by
  sorry

/-- (274): the box wire is an identity wire; the box moves to an idle wire. -/
theorem eq274 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .box [1] (blackOn 2 N)) (mc N .box [0] (blackOn 2 N)) := by
  sorry

/-- (277): the same for the box of the multi-controlled `H`. -/
theorem eq277 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .hg [1, 2] (blackOn 3 N)) (mc N .hg [0, 2] (blackOn 3 N)) := by
  sorry

/-- (299): the box is an involution. -/
theorem eq299 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [Bx N, Bx N]) 1 := by
  sorry

/-- (305). -/
theorem eq305 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [mc N .xz [0] (ctlAt 1 true), mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .zx [0] (ctlAt 1 true), mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))])
      (Bx N) := by
  sorry

/-- (307): the box commutes with the swap of two of its controls (with (81),
its controls may be permuted). -/
theorem eq307 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (j : ℕ) (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    Derivable (theory N) (drawn [Bx N, swAt N j]) (drawn [swAt N j, Bx N]) := by
  sorry

/-- (308), Lemma D.9: any circuit on the bottom `m` wires commutes with the
box whose box wire is wire `m - 1` and whose controls are the wires above. -/
theorem eq308 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N)
    (C : Circ m) :
    Derivable (theory N) (drawn [atBot N C, mc N .box [m - 1] (blackOn m N)])
      (drawn [mc N .box [m - 1] (blackOn m N), atBot N C]) := by
  sorry

/-- (309): a black and a white control on the same wire `w` merge. -/
theorem eq309 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) (w : ℕ) (hw : 1 ≤ w)
    (hwN : w < N) (b : Bool) :
    Derivable (theory N)
      (drawn [mc N .box [0] (setCtl (colOn 1 N x) w (some b)),
        mc N .box [0] (setCtl (colOn 1 N x) w (some !b))])
      (mc N .box [0] (setCtl (colOn 1 N x) w none)) := by
  sorry

/-- (310): the same for the multi-controlled `H`. -/
theorem eq310 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) (w : ℕ) (hw : 2 ≤ w)
    (hwN : w < N) (b : Bool) :
    Derivable (theory N)
      (drawn [mc N .hg [0, 1] (setCtl (colOn 2 N x) w (some b)),
        mc N .hg [0, 1] (setCtl (colOn 2 N x) w (some !b))])
      (mc N .hg [0, 1] (setCtl (colOn 2 N x) w none)) := by
  sorry

/-- (311): a coloured box is an involution. -/
theorem eq311 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Derivable (theory N) (drawn [mc N .box [0] (colOn 1 N x), mc N .box [0] (colOn 1 N x)]) 1 := by
  sorry

/-- (312): a coloured multi-controlled `H` is an involution. -/
theorem eq312 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Derivable (theory N)
      (drawn [mc N .hg [0, 1] (colOn 2 N x), mc N .hg [0, 1] (colOn 2 N x)]) 1 := by
  sorry

/-- (313): the multi-controlled `H` commutes with the swap of two of its
controls. -/
theorem eq313 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (j : ℕ) (hj : 2 ≤ j) (hjN : j + 2 ≤ N) :
    Derivable (theory N) (drawn [mc N .hg [0, 1] (blackOn 2 N), swAt N j])
      (drawn [swAt N j, mc N .hg [0, 1] (blackOn 2 N)]) := by
  sorry

/-- (314), Lemma D.11: any circuit on the bottom `m` wires commutes with the
multi-controlled `H` whose box is on wire `m - 1`, its `H` on wire `m`. -/
theorem eq314 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (m : ℕ) (hm : 1 ≤ m) (hmN : m + 1 ≤ N)
    (C : Circ m) :
    Derivable (theory N) (drawn [atBot N C, mc N .hg [m - 1, m] (blackOn (m + 1) N)])
      (drawn [mc N .hg [m - 1, m] (blackOn (m + 1) N), atBot N C]) := by
  sorry

end QCert.RealCliffordCH.Sec8.D
