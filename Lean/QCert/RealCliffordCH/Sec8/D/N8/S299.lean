/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (289), (293), (295)–(299) at every width

On five local wires.  The route to (299) is the paper's from (295) on, with
(289) and the box commutation behind (291) proved more directly.

* (289), the box on wire `0` with controls `1, 2, 3` against the box on
  wire `2` with controls `0, 3, 4` and the bulk (`s289`): the first is
  `[CZ₀₂, ZX₀ controlled by 1, 3]` one width down (Lemma 5.1); the second
  passes `CZ₀₂` by Lemma 5.1 and carries the `ZX` to itself times a box with
  an idle wire, which passes `CZ₀₂` by (272) relabeled (`sL2`).
* The `ZX` on wire `1` with controls `0, 2, 3` passes the box `C` of (269)
  (`s291c`, (291) relabeled): it is `t β t β` with `t` the `CH` from wire `0`
  and `β` the box on wire `0` with controls `1, 2, 3`; `C` passes `t` by
  Lemma 5.1 and `β` by (289), its box wire moved by (274).  With a white
  control on wire `2` (`sAbC`) it is the black one inverted times the one
  without a control on wire `2`.
* (293), that `ZX` white on wire `2` passes the box (`s293`): it passes
  `W`, `V` (Lemma 5.1) and `C` (`sAbC`).
* (295), in the form of the second line of the paper's proof (`s295`): the
  box conjugated by that `ZX` ((293)), (294) (that is (269) with `C`
  written by (269) one width down), and Lemma 5.1 to merge the colours.
* (296), the `H` on wire `0` white-controlled by wire `2` passes the box
  (`s296`): it passes each factor of (295) by Lemma 5.1.  (297) is (296)
  under the swap of the wires `1, 2` ((275), `s297`), (298) is (285) and
  (297) (`s298`), and (299), the box is an involution, is (286), (273) and
  (298) (`s299`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.S285

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

abbrev lS0 : Lt := .s (.S 0)

/-! ## (289) -/

/-- The box on wire `0`, controls `1, 2, 3` (no bulk). -/
def bQ1 : Lt := .g .box [0] [(1, true), (2, true), (3, true)] false
/-- The `ZX` and `XZ` on wire `0`, controls `1, 3`. -/
def z13 : Lt := .g .zx [0] [(1, true), (3, true)] false
def x13 : Lt := .g .xz [0] [(1, true), (3, true)] false

def T289 : SE.Tbl := [([a2], [b2]), ([c3, eA], [eA, c3])]

theorem T289_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T289 := by
  intro e he
  simp only [T289, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s274r m ih
  · exact sL2 m ih

theorem run289 : check 4 T289 [bQ1, a2] [a2, bQ1]
    [.sem 0 1 [c3, x13, c3, z13] 4, .rw 4 0 false, .sem 3 2 [cC, eA, z13] 2, .rw 3 0 true,
     .sem 2 2 [a2, c3] 1, .rw 2 0 false, .sem 1 2 [cC, eA, x13] 2, .rw 1 0 true,
     .sem 0 2 [a2, c3] 1, .sem 2 2 [x13, eA] 2, .rw 3 1 true, .sem 4 2 [] 2,
     .sem 1 4 [bQ1] 4] = true := by
  decide +kernel

/-- (289) on five local wires. -/
theorem s289 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bQ1, a2]) (wc 5 (m + 5) [a2, bQ1]) :=
  check_sound (frame 4) ih (T289_ok m ih) run289

/-! ## The `ZX` on wire `1` against `C` -/

/-- The `ZX`, `XZ` on wire `1` with controls `0, 2, 3`. -/
def A2z : Lt := .g .zx [1] [(0, true), (2, true), (3, true)] false
def A2x : Lt := .g .xz [1] [(0, true), (2, true), (3, true)] false
/-- The same, white on wire `2`. -/
def Abz : Lt := .g .zx [1] [(0, true), (2, false), (3, true)] false
def Abx : Lt := .g .xz [1] [(0, true), (2, false), (3, true)] false
/-- The `ZX`, `XZ` on wire `1` with controls `0, 3`. -/
def A1z : Lt := .g .zx [1] [(0, true), (3, true)] false
def A1x : Lt := .g .xz [1] [(0, true), (3, true)] false

def T291c : SE.Tbl := [([a2], [b2]), ([bQ1, a2], [a2, bQ1])]

theorem T291c_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T291c := by
  intro e he
  simp only [T291c, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s274r m ih
  · exact s289 m ih

theorem run291c : check 4 T291c [A2z, cC] [cC, A2z]
    [.sem 0 1 [lS0, lK0, lS0, bQ1, lS0, lK0, lS0, bQ1] 4, .rw 8 0 true, .rw 7 1 false,
     .rw 7 0 false, .sem 4 4 [cC, lS0, lK0, lS0] 2, .rw 4 0 true, .rw 3 1 false, .rw 3 0 false,
     .sem 0 4 [cC, lS0, lK0, lS0] 2, .sem 1 8 [A2z] 4] = true := by
  decide +kernel

theorem s291c (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [A2z, cC]) (wc 5 (m + 5) [cC, A2z]) :=
  check_sound (frame 4) ih (T291c_ok m ih) run291c

def TAbC : SE.Tbl := [([A2z, cC], [cC, A2z])]

theorem TAbC_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TAbC := by
  intro e he
  simp only [TAbC, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl
  exact s291c m ih

theorem runAbC : check 4 TAbC [Abz, cC] [cC, Abz]
    [.sem 0 1 [A2x, A1z] 4, .sem 1 2 [cC, A1z] 2, .sem 2 0 [A2z, A2x] 4, .rw 1 0 true,
     .sem 0 2 [] 4, .sem 1 2 [Abz] 4] = true := by
  decide +kernel

theorem sAbC (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Abz, cC]) (wc 5 (m + 5) [cC, Abz]) :=
  check_sound (frame 4) ih (TAbC_ok m ih) runAbC

/-! ## (293) and (295) -/

def T293 : SE.Tbl := [([bx0], [wW, cC, wV, cC]), ([Abz, cC], [cC, Abz])]

theorem T293_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T293 := by
  intro e he
  simp only [T293, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact t269 m
  · exact sAbC m ih

theorem run293 : check 4 T293 [Abz, bx0] [bx0, Abz]
    [.rw 1 0 false, .sem 0 2 [wW, Abz] 4, .rw 1 1 false, .sem 2 2 [wV, Abz] 4, .rw 3 1 false,
     .rw 0 0 true] = true := by
  decide +kernel

/-- (293) on five local wires. -/
theorem s293 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Abz, bx0]) (wc 5 (m + 5) [bx0, Abz]) :=
  check_sound (frame 4) ih (T293_ok m ih) run293

/-- The box on wire `0`, controls `1, 4` and the bulk. -/
def D4 : Lt := .g .box [0] [(1, true), (4, true)] true

/-- The factors of (295) (second line of its proof). -/
def F295 : List Lt := [wW, A2z, D4, A2x, wV, A2z, D4, A2x]

def T295 : SE.Tbl := [([bx0], [wW, cC, wV, cC]), ([Abz, bx0], [bx0, Abz])]

theorem T295_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T295 := by
  intro e he
  simp only [T295, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact t269 m
  · exact s293 m ih

theorem run295 : check 4 T295 [bx0] F295
    [.sem 0 0 [Abx, Abz] 4, .rw 1 1 false, .rw 1 0 false, .sem 2 1 [A1z, D4, A1x, D4] 2,
     .sem 7 1 [A1z, D4, A1x, D4] 2, .sem 5 2 [wV, D4] 3, .sem 6 5 [A1z, D4, A1x] 2,
     .sem 0 2 [wW, Abx] 4, .sem 1 2 [A2z] 4, .sem 7 2 [A2x] 4,
     .sem 3 3 [A2x, wV, A2z] 4] = true := by
  decide +kernel

/-- (295) on five local wires, in the form of the second line of its proof. -/
theorem s295 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0]) (wc 5 (m + 5) F295) :=
  check_sound (frame 4) ih (T295_ok m ih) run295

/-! ## (296)–(299) -/

/-- `H` on wire `0`, white-controlled by wire `2` (box wire `1`). -/
def hW : Lt := .g .hg [1, 0] [(2, false)] false
/-- `H` on wire `0`, white-controlled by wire `1` (box wire `2`). -/
def hW1 : Lt := swapG 1 .hg [1, 0] [(2, false)] false

def T296 : SE.Tbl := [([bx0], F295)]

theorem T296_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T296 := by
  intro e he
  simp only [T296, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl
  exact s295 m ih

theorem run296 : check 4 T296 [hW, bx0] [bx0, hW]
    [.rw 1 0 false, .sem 0 2 [wW, hW] 3, .sem 1 2 [A2z, hW] 4, .sem 2 2 [D4, hW] 3,
     .sem 3 2 [A2x, hW] 4, .sem 4 2 [wV, hW] 3, .sem 5 2 [A2z, hW] 4, .sem 6 2 [D4, hW] 3,
     .sem 7 2 [A2x, hW] 4, .rw 0 0 true] = true := by
  decide +kernel

/-- (296) on five local wires. -/
theorem s296 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [hW, bx0]) (wc 5 (m + 5) [bx0, hW]) :=
  check_sound (frame 4) ih (T296_ok m ih) run296

def T297 : SE.Tbl :=
  [([hW, bx0], [bx0, hW]), ([bx0, lS1], [lS1, bx0]), ([lS1, hW, lS1], [hW1])]

theorem T297_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T297 := by
  intro e he
  simp only [T297, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact s296 m ih
  · exact s275 m ih
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)

theorem run297 : check 4 T297 [hW1, bx0] [bx0, hW1]
    [.rw 0 2 true, .rw 2 1 true, .rw 1 0 false, .rw 0 1 true, .rw 1 2 false] = true := by
  decide +kernel

/-- (297) on five local wires. -/
theorem s297 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [hW1, bx0]) (wc 5 (m + 5) [bx0, hW1]) :=
  check_sound (frame 4) ih (T297_ok m ih) run297

def T298 : SE.Tbl := [([lH0, bx0], [bx0, lH0]), ([hW1, bx0], [bx0, hW1])]

theorem T298_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T298 := by
  intro e he
  simp only [T298, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s285 m ih
  · exact s297 m ih

theorem run298 : check 4 T298 [lK0, bx0] [bx0, lK0]
    [.sem 0 1 [lH0, hW1] 3, .rw 1 1 false, .rw 0 0 false, .sem 1 2 [lK0] 3] = true := by
  decide +kernel

/-- (298) on five local wires: `CH` from wire `1` onto the box wire passes
the box. -/
theorem s298 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [lK0, bx0]) (wc 5 (m + 5) [bx0, lK0]) :=
  check_sound (frame 4) ih (T298_ok m ih) run298

def T299 : SE.Tbl :=
  [([bx0], [wW, cC, wV, cC]), ([bx0], [wV, cC, wW, cC]), (cz02L ++ [bx0], [bx0] ++ cz02L),
   ([lK0, bx0], [bx0, lK0])]

theorem T299_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T299 := by
  intro e he
  simp only [T299, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact t269 m
  · exact s286 m ih
  · exact s273 m ih
  · exact s298 m ih

theorem run299 : check 4 T299 [bx0, bx0] []
    [.rw 1 1 false, .sem 1 1 [lS1, lC0, lS1, lK0, lS1, lC0, lS1, lK0] 3, .rw 0 2 true,
     .rw 3 3 true, .rw 4 2 true, .rw 7 3 true, .sem 0 8 [wV] 3, .rw 1 0 false, .sem 0 2 [] 3,
     .sem 2 2 [] 2, .sem 1 2 [] 3, .sem 0 2 [] 2] = true := by
  decide +kernel

/-- (299) on five local wires: the box is an involution. -/
theorem s299 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0, bx0]) (wc 5 (m + 5) []) :=
  check_sound (frame 4) ih (T299_ok m ih) run299

end QCert.RealCliffordCH.Sec8.D.N8
