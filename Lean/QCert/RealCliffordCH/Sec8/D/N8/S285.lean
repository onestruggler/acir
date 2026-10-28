/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (280) and (285) at every width

On five local wires.  Neither follows the paper's route ((280) through
(279), (278); (285) through (284), (283)).

* (280), `CH` from the idle wire onto the box wire passes the box (`s280`):
  `CH` is a word in `H` and `Z` on either wire, `CZ` and `P ⊗ P` on the
  wires `0, 1` (found by a search over that group), and each of these passes
  the box: a one-wire gate by Lemma 5.1, with the box wire moved away from
  it by (274); `CZ` by (272); `P ⊗ P` by (276).
* (285), `H` on the box wire passes the box (`s285`): `H` exchanges `W` and
  `V` and carries `C` to `C R`, `R` the multi-controlled `XZ` on wire `0`
  (controls `3, 4` and the bulk), so by (286) it is enough that `R` passes
  `V = c t c t` (`c` the `CZ` of the wires `0, 2`, `t` the `CH` from wire
  `1`).  `R` carries `c` to `c e'` and `t` to `t e`, `e'` and `e` boxes with
  an idle wire (Lemma 5.1), and `e'` passes `t` by (280), `e` passes `c` by
  (272) relabeled, `e` and `e'` commute (Lemma 5.1, their box wires moved
  apart by (274)) (`sCore`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.S275
import QCert.RealCliffordCH.Sec8.D.N8.S277

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

abbrev lH0 : Lt := .s (.H 0)
abbrev lH1 : Lt := .s (.H 1)
abbrev lC0 : Lt := .s (.C 0)
abbrev lK0 : Lt := .s (.K 0)
abbrev lS1 : Lt := .s (.S 1)

/-! ## (280) -/

/-- `CH` from wire `1` onto wire `0`, as a word in `H`, `CZ` and `P ⊗ P`. -/
def wK : List Lt := [lH1, lC0, lH0, lC0] ++ ppL 0 ++ [lC0, lH0, lC0, lH0, lH1, lC0]

def T280 : SE.Tbl := [([lC0, B0], [B0, lC0]), ([B1], [B0]), (ppL 0 ++ [B1] ++ ppL 0, [B1])]

theorem T280_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T280 := by
  intro e he
  simp only [T280, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact s272 m ih
  · exact s274 m ih
  · exact s276 m ih

theorem run280 : check 4 T280 [lK0, B0] [B0, lK0]
    [.sem 0 1 wK 2,
     .rw 19 0 false, .rw 19 1 true, .sem 18 2 [B1, lH1] 0, .rw 18 1 false,
     .sem 17 2 [B0, lH0] 1, .rw 16 0 false, .sem 15 2 [B0, lH0] 1, .rw 14 0 false,
     .rw 14 1 true, .sem 15 0 (ppL 0 ++ ppL 0) 2,
     .rw 4 2 false, .rw 4 1 false, .rw 3 0 false, .sem 2 2 [B0, lH0] 1, .rw 1 0 false,
     .rw 1 1 true, .sem 0 2 [B1, lH1] 0, .rw 0 1 false, .sem 1 20 [lK0] 2] = true := by
  decide +kernel

/-- (280) on five local wires: `CH` from the idle wire `1` onto the box wire
`0` passes the box `B0`. -/
theorem s280 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [lK0, B0]) (wc 5 (m + 5) [B0, lK0]) :=
  check_sound (frame 4) ih (T280_ok m ih) run280

/-! ## (285) -/

/-- The box on wire `0`, controls `1, 3, 4` and the bulk, wire `2` idle. -/
def eA : Lt := swapG 1 .box [0] [(2, true), (3, true), (4, true)] true
/-- The box on wire `2`, controls `1, 3, 4` and the bulk, wire `0` idle. -/
def eA2 : Lt := swapG 1 .box [1] [(2, true), (3, true), (4, true)] true
/-- `CZ` of the wires `0, 2`, as a box with box wire `3`. -/
def c3 : Lt := .g .box [3] [(0, true), (2, true)] false
/-- The multi-controlled `XZ` and `ZX` on wire `0`, controls `3, 4` and the
bulk. -/
def Rx : Lt := .g .xz [0] [(3, true), (4, true)] true
def Rz : Lt := .g .zx [0] [(3, true), (4, true)] true

/-- (272) relabeled: `CZ` of the wires `0, 2` passes `eA`. -/
def TL2 : SE.Tbl := [([lC0, B0], [B0, lC0]), ([lS1, eA, lS1], [B0])]

theorem TL2_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TL2 := by
  intro e he
  simp only [TL2, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s272 m ih
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)

theorem runL2 : check 4 TL2 [c3, eA] [eA, c3]
    [.sem 0 1 [lS1, lC0, lS1] 4, .sem 4 0 [lS1, lS1] 4, .rw 2 1 false, .rw 1 0 false,
     .rw 1 1 true, .sem 0 2 [] 4, .sem 1 3 [c3] 4] = true := by
  decide +kernel

theorem sL2 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [c3, eA]) (wc 5 (m + 5) [eA, c3]) :=
  check_sound (frame 4) ih (TL2_ok m ih) runL2

/-- `eA` and `B0` commute. -/
def TL3 : SE.Tbl := [([B1], [B0]), ([lS1, B0, lS1], [eA]), ([lS1, B1, lS1], [eA2])]

theorem TL3_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TL3 := by
  intro e he
  simp only [TL3, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact s274 m ih
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)

theorem runL3 : check 4 TL3 [eA, B0] [B0, eA]
    [.rw 0 1 true, .rw 1 0 true, .rw 0 2 false, .rw 1 0 true, .sem 0 2 [B1, eA2] 0,
     .rw 0 0 false, .rw 1 2 true, .rw 2 0 false, .rw 1 1 false] = true := by
  decide +kernel

theorem sL3 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [eA, B0]) (wc 5 (m + 5) [B0, eA]) :=
  check_sound (frame 4) ih (TL3_ok m ih) runL3

/-- `R` passes `V`. -/
def TCore : SE.Tbl := [([lK0, B0], [B0, lK0]), ([c3, eA], [eA, c3]), ([eA, B0], [B0, eA])]

theorem TCore_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TCore := by
  intro e he
  simp only [TCore, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact s280 m ih
  · exact sL2 m ih
  · exact sL3 m ih

theorem runCore : check 4 TCore [Rx, wV, Rz] [wV]
    [.sem 1 1 [c3, lK0, c3, lK0] 4, .sem 0 2 [c3, B0, Rx] 1, .sem 2 2 [lK0, eA, Rx] 2,
     .sem 4 2 [c3, B0, Rx] 1, .sem 6 2 [lK0, eA, Rx] 2, .sem 8 2 [] 2, .rw 3 1 true,
     .rw 4 2 false, .sem 5 3 [lK0] 2, .rw 1 0 true, .sem 2 3 [c3] 1,
     .sem 0 4 [wV] 4] = true := by
  decide +kernel

theorem sCore (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Rx, wV, Rz]) (wc 5 (m + 5) [wV]) :=
  check_sound (frame 4) ih (TCore_ok m ih) runCore

def T285 : SE.Tbl :=
  [([bx0], [wW, cC, wV, cC]), ([bx0], [wV, cC, wW, cC]), ([Rx, wV, Rz], [wV])]

theorem T285_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T285 := by
  intro e he
  simp only [T285, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact t269 m
  · exact s286 m ih
  · exact sCore m ih

theorem run285 : check 4 T285 [lH0, bx0] [bx0, lH0]
    [.rw 1 1 false, .sem 0 2 [wW, lH0] 3, .sem 1 2 [cC, Rx, lH0] 2, .sem 3 2 [wV, lH0] 3,
     .sem 4 2 [cC, Rx, lH0] 2, .sem 4 2 [Rz, cC] 2, .rw 2 2 false, .rw 0 0 true] = true := by
  decide +kernel

/-- (285) on five local wires: `H` on the box wire passes the box. -/
theorem s285 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [lH0, bx0]) (wc 5 (m + 5) [bx0, lH0]) :=
  check_sound (frame 4) ih (T285_ok m ih) run285

end QCert.RealCliffordCH.Sec8.D.N8
