/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.5–D.6 (Lemmas D.8–D.11): the interface of package (iv)

The equations of Lemmas D.8–D.11 that later packages use, stated on `N`
wires with completeness on fewer wires as a hypothesis (`IH N`, Lemma 5.1),
in the conventions of `MC` (see `PLAN.md`): `mc N K tg c` is the
multi-controlled gate of kind `K` with special wires `tg` (box wire; target;
box wire then `H` wire) and controls `c`.  Every statement here was checked
numerically against the definitions at `N = 3, …, 6` (scratch
`r87/iface.py`). Every statement is proved, by cases on the width where
needed: three and four wires in `N8/Low`, `MoreLow`, `ControlFour` and
`Four295`, five wires on in `N8/IFive`.
-/
import QCert.RealCliffordCH.Sec8.D.Colour
import QCert.RealCliffordCH.Sec8.D.N8.I277
import QCert.RealCliffordCH.Sec8.D.N8.I269
import QCert.RealCliffordCH.Sec8.D.N8.I310
import QCert.RealCliffordCH.Sec8.D.N8.Low
import QCert.RealCliffordCH.Sec8.D.N8.Below
import QCert.RealCliffordCH.Sec8.D.N8.MergeHg
import QCert.RealCliffordCH.Sec8.D.N8.MoreLow
import QCert.RealCliffordCH.Sec8.D.N8.ControlFour
import QCert.RealCliffordCH.Sec8.D.N8.Four295
import QCert.RealCliffordCH.Sec8.D.W4.B1

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

/-- The box on wire `0` with black controls on every other wire. -/
abbrev Bx (N : ℕ) : Circ N := mc N .box [0] (blackOn 1 N)

/-- (81), for every multi-controlled gate: `X` on a control wire on both
sides exchanges the colour of that control. -/
theorem eq81 (N : ℕ) (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool) (j : ℕ) (b : Bool)
    (hj : j < N) (hjt : j ∉ tg) (hc : c j = some b) :
    Derivable (theory N) (drawn [xAt N j, mc N K tg c, xAt N j])
      (mc N K tg (setCtl c j (some !b))) :=
  eq81' N K tg c j b hj hjt hc

/-- The box on wire `1` with controls on wire `0` and on the wires `3, …, N - 1`
(the inner box of (269) and (300)). -/
abbrev Bx1 (N : ℕ) : Circ N := mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 3 N))

/-- (269), Definition 2.4 in the conventions of `MC`: the box is
`W B V B`, `W` and `V` the doubly controlled `ZX` and `XZ` on wire `0`
(controls `1`, `2`), `B` the box on wire `1` (controls `0`, `3, …`). -/
theorem eq269 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (Bx N)
      (drawn [mc N .zx [0] (blackOn 1 3), Bx1 N, mc N .xz [0] (blackOn 1 3), Bx1 N]) :=
  N8.eq269' N hN ih

/-- (290): the box without controls on the wires `2`, `3` commutes with the
`ZX` controlled by the wires `1, 2, 3`. -/
theorem eq290 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [mc N .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 N)), mc N .zx [0] (blackOn 1 4)])
      (drawn [mc N .zx [0] (blackOn 1 4), mc N .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 N))]) := by
  rcases (by omega : N = 4 ∨ 5 ≤ N) with rfl | h5
  · exact N8.eq290_4 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq290_5 m ih

/-- (291): the box without a control on wire `2` commutes with the `ZX`
controlled by the wires `1, 2, 3`. -/
theorem eq291 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [mc N .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 N)), mc N .zx [0] (blackOn 1 4)])
      (drawn [mc N .zx [0] (blackOn 1 4), mc N .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 N))]) := by
  rcases (by omega : N = 4 ∨ 5 ≤ N) with rfl | h5
  · exact N8.eq291_4 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq291_5 m ih

/-- (292): the `ZX` controlled by the wires `1, 2` commutes with the box on
wire `1` with a white control on wire `2` (black on `0` and `3, …`). -/
theorem eq292 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [mc N .zx [0] (blackOn 1 3),
        mc N .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 N)))])
      (drawn [mc N .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 N))),
        mc N .zx [0] (blackOn 1 3)]) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N8.eq292_3 ih
  · exact N8.eq292_4 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq292_5 m ih

/-- (295): the box written with `ZX` and `XZ` gates on wires `0`, `1` and the
box without controls on the wires `2`, `3`. -/
theorem eq295 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) :
    Derivable (theory N) (Bx N)
      (drawn [mc N .zx [0] (blackOn 1 4), mc N .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)),
        mc N .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 N)),
        mc N .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)), mc N .xz [0] (blackOn 1 4),
        mc N .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)),
        mc N .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 N)),
        mc N .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4))]) := by
  rcases (by omega : N = 4 ∨ 5 ≤ N) with rfl | h5
  · exact N8.eq295_4 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq295_5 m ih

/-- (300): (269) with the factors rotated, `B W B V`. -/
theorem eq300 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (Bx N)
      (drawn [Bx1 N, mc N .zx [0] (blackOn 1 3), Bx1 N, mc N .xz [0] (blackOn 1 3)]) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · set_option maxRecDepth 100000 in
      exact N8.t300 ih
  · exact N8.eq300_4 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq300_5 m ih

/-- (301): the box followed by its version white on wire `2` is the box
without a control on wire `2`. -/
theorem eq301 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [Bx N, mc N .box [0] (setCtl (blackOn 1 N) 2 (some false))])
      (mc N .box [0] (setCtl (blackOn 1 N) 2 none)) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N8.eq301_3 ih
  · exact N8.eq301_4 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq301_5 m ih

/-- (302): (301) in the other order. -/
theorem eq302 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [mc N .box [0] (setCtl (blackOn 1 N) 2 (some false)), Bx N])
      (mc N .box [0] (setCtl (blackOn 1 N) 2 none)) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N8.eq302_3 ih
  · exact N8.eq302_4 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq302_5 m ih

/-- (274): the box wire is an identity wire; the box moves to an idle wire. -/
theorem eq274 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .box [1] (blackOn 2 N)) (mc N .box [0] (blackOn 2 N)) :=
  N8.eq274' N hN ih

/-- (277): the same for the box of the multi-controlled `H`. -/
theorem eq277 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .hg [1, 2] (blackOn 3 N)) (mc N .hg [0, 2] (blackOn 3 N)) :=
  N8.eq277' N hN ih

/-- (299): the box is an involution. -/
theorem eq299 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [Bx N, Bx N]) 1 := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · have hB : Bx 3 = Circuit.shift (cz : Circ 2) := by
      exact (Net.mc_canon .box 2)
    rw [hB]
    have h := sem_step_shift ih (Fast.sem_of_fast
      (w := (cz : Circ 2) * cz) (w' := 1) (by decide +kernel))
    simpa [drawn] using h
  · set_option maxRecDepth 100000 in
      exact W4.t166 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq299_5 m ih

/-- (305). -/
theorem eq305 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [mc N .xz [0] (ctlAt 1 true), mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .zx [0] (ctlAt 1 true), mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))])
      (Bx N) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N8.eq305_3 ih
  · exact N8.eq305_4 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    exact N8.eq305_5 m ih

/-- (307): the box commutes with the swap of two of its controls (with (81),
its controls may be permuted). -/
theorem eq307 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (j : ℕ) (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    Derivable (theory N) (drawn [Bx N, swAt N j]) (drawn [swAt N j, Bx N]) := by
  exact N8.eq307_all N hN ih j hj hjN

/-- (308), Lemma D.9: any circuit on the bottom `m` wires commutes with the
box whose box wire is wire `m - 1` and whose controls are the wires above. -/
theorem eq308 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N)
    (C : Circ m) :
    Derivable (theory N) (drawn [atBot N C, mc N .box [m - 1] (blackOn m N)])
      (drawn [mc N .box [m - 1] (blackOn m N), atBot N C]) := by
  exact N8.eq308_all N hN ih m hm hmN C

/-- (309): a black and a white control on the same wire `w` merge. -/
theorem eq309 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) (w : ℕ) (hw : 1 ≤ w)
    (hwN : w < N) (b : Bool) :
    Derivable (theory N)
      (drawn [mc N .box [0] (setCtl (colOn 1 N x) w (some b)),
        mc N .box [0] (setCtl (colOn 1 N x) w (some !b))])
      (mc N .box [0] (setCtl (colOn 1 N x) w none)) := by
  exact N8.eq309_of hN (eq307 N hN ih) (eq301 N hN ih) (eq302 N hN ih) x w hw hwN b

/-- (310): the same for the multi-controlled `H`. -/
theorem eq310 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) (w : ℕ) (hw : 2 ≤ w)
    (hwN : w < N) (b : Bool) :
    Derivable (theory N)
      (drawn [mc N .hg [0, 1] (setCtl (colOn 2 N x) w (some b)),
        mc N .hg [0, 1] (setCtl (colOn 2 N x) w (some !b))])
      (mc N .hg [0, 1] (setCtl (colOn 2 N x) w none)) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact N8.eq310_3 ih x w hw hwN b
  · exact N8.eq310_4 ih (eq309 4 (by omega) ih) x w hw hwN b
  · exact N8.eq310_of h5 ih (eq309 N hN ih) x w hw hwN b

/-- (311): a coloured box is an involution. -/
theorem eq311 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Derivable (theory N) (drawn [mc N .box [0] (colOn 1 N x), mc N .box [0] (colOn 1 N x)]) 1 := by
  exact N8.eq311_of (eq299 N hN ih) x

/-- (312): a coloured multi-controlled `H` is an involution. -/
theorem eq312 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Derivable (theory N)
      (drawn [mc N .hg [0, 1] (colOn 2 N x), mc N .hg [0, 1] (colOn 2 N x)]) 1 := by
  rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | h4
  · exact N8.eq312_3 ih x
  · exact N8.eq312_of h4 ih (eq311 N hN ih) x

/-- (313): the multi-controlled `H` commutes with the swap of two of its
controls. -/
theorem eq313 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (j : ℕ) (hj : 2 ≤ j) (hjN : j + 2 ≤ N) :
    Derivable (theory N) (drawn [mc N .hg [0, 1] (blackOn 2 N), swAt N j])
      (drawn [swAt N j, mc N .hg [0, 1] (blackOn 2 N)]) := by
  exact N8.eq313_of (by omega) (eq307 N hN ih) j hj hjN

/-- (314), Lemma D.11: any circuit on the bottom `m` wires commutes with the
multi-controlled `H` whose box is on wire `m - 1`, its `H` on wire `m`. -/
theorem eq314 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (m : ℕ) (hm : 1 ≤ m) (hmN : m + 1 ≤ N)
    (C : Circ m) :
    Derivable (theory N) (drawn [atBot N C, mc N .hg [m - 1, m] (blackOn (m + 1) N)])
      (drawn [mc N .hg [m - 1, m] (blackOn (m + 1) N), atBot N C]) := by
  exact N8.eq314_all N hN ih m hm hmN C

end QCert.RealCliffordCH.Sec8.D
