/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (290)–(292), (295), (305), (306) at every width from five

On five local wires.

* (291) in the conventions of the interface (`s291i`): `S299.s291c` (its
  relabeled version) conjugated by the swap of the wires `0, 1`; with `XZ`
  in place of `ZX` (`s291x`).
* (290), the box `D4` (controls `1, 4` and the bulk) passes the `ZX` on wire
  `0` controlled by `1, 2, 3` (`s290`): `D4` is the box `eA` (controls
  `1, 3, 4`, bulk) times its version white on wire `3` (Lemma 5.1); `eA`
  passes the `ZX` by (291), and the white one, conjugated by `X` on wire `3`,
  is `eA` against the `ZX` white on wire `3`, which is `W` times the `XZ`
  controlled by `1, 2, 3` (Lemma 5.1), passed by (287) and (291).  Not the
  paper's route through (288).
* (295) in the form of the interface (`s295i`): from `S299.s295` (the second
  line of the paper's proof), splitting `W` into its two colours on wire
  `3` and carrying the white one across by Lemma 5.1 and (290) white on
  wire `3` (`s290w`).
* (306), the box commutes with the swap of the wires `2, 3` (`s306`): every
  factor of (295) does (the paper's proof, with (214) a semantic step).
* (292), `W` passes the box on wire `1` white on wire `2` (`s292`): that box
  is (269) conjugated by `X` on wire `2` and the swap of the wires `0, 1`
  (`s269Bw`), whose factors `W` passes by Lemma 5.1 and (287).
* (305) (`s305`): the paper's proof.  The white parts of `XZ(0 | 1)` and
  `ZX(0 | 1)` pass the box on wire `1` (`sVbBf`, the analogue of (292)), the
  box white on wire `2` is an involution (`sBw2`), (292), and (301), (302)
  relabeled (`s301r`, `s302r`) merge the boxes into the `C` of (286).
-/
import QCert.RealCliffordCH.Sec8.D.N8.S300

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

abbrev lS2 : Lt := .s (.S 2)

/-- `ZX`, `XZ` on wire `0` controlled by `1, 2, 3`. -/
def Z123 : Lt := .g .zx [0] [(1, true), (2, true), (3, true)] false
def X123 : Lt := .g .xz [0] [(1, true), (2, true), (3, true)] false
/-- The box `eA` white on wire `3`. -/
def D3w : Lt := .g .box [0] [(1, true), (3, false), (4, true)] true
/-- `ZX` on wire `0` controlled by `1, 2` and white on `3`. -/
def Zw : Lt := .g .zx [0] [(1, true), (2, true), (3, false)] false

/-! ## (291) -/

def T291i : SE.Tbl := [([lS0, cC, lS0], [eA]), ([lS0, A2z, lS0], [Z123]), ([A2z, cC], [cC, A2z])]

theorem T291i_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T291i := by
  intro e he
  simp only [T291i, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
  · exact s291c m ih

theorem run291i : check 4 T291i [eA, Z123] [Z123, eA]
    [.rw 0 0 true, .rw 3 1 true, .sem 2 2 [] 4, .rw 1 2 true, .sem 2 0 [lS0, lS0] 4,
     .rw 0 1 false, .rw 1 0 false] = true := by
  decide +kernel

/-- (291) on five local wires, as in the interface. -/
theorem s291i (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [eA, Z123]) (wc 5 (m + 5) [Z123, eA]) :=
  check_sound (frame 4) ih (T291i_ok m ih) run291i

def T291x : SE.Tbl := [([eA, Z123], [Z123, eA])]

theorem T291x_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T291x := by
  intro e he
  simp only [T291x, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl
  exact s291i m ih

theorem run291x : check 4 T291x [eA, X123] [X123, eA]
    [.sem 0 0 [X123, Z123] 4, .rw 1 0 true, .sem 2 2 [] 4] = true := by
  decide +kernel

theorem s291x (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [eA, X123]) (wc 5 (m + 5) [X123, eA]) :=
  check_sound (frame 4) ih (T291x_ok m ih) run291x

/-! ## (290) -/

theorem x81_eA3 (m : ℕ) : Derivable (theory (m + 5)) (wc 5 (m + 5) (xL 3 ++ [eA] ++ xL 3))
    (wc 5 (m + 5) [D3w]) :=
  x81E m 5 3 (by omega) .box [0] _ _ true true (by decide) (by decide) (by decide)

def T290 : SE.Tbl :=
  [([eA, Z123], [Z123, eA]), ([eA, X123], [X123, eA]), ([eA, wW], [wW, eA]),
   (xL 3 ++ [eA] ++ xL 3, [D3w])]

theorem T290_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T290 := by
  intro e he
  simp only [T290, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact s291i m ih
  · exact s291x m ih
  · exact s287 m ih
  · exact x81_eA3 m

theorem run290 : check 4 T290 [D4, Z123] [Z123, D4]
    [.sem 0 1 [eA, D3w] 2, .rw 1 3 true, .sem 5 4 [Zw, .s (.H 3), .s (.Z 3), .s (.H 3)] 4,
     .sem 5 1 [wW, X123] 4, .rw 4 2 false, .rw 5 1 false, .sem 4 2 [Zw] 4,
     .sem 1 4 [Z123, .s (.H 3), .s (.Z 3), .s (.H 3)] 4, .rw 2 3 false, .rw 0 0 false,
     .sem 1 2 [D4] 2] = true := by
  decide +kernel

/-- (290) on five local wires. -/
theorem s290 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [D4, Z123]) (wc 5 (m + 5) [Z123, D4]) :=
  check_sound (frame 4) ih (T290_ok m ih) run290

def T290w : SE.Tbl :=
  [([D4, Z123], [Z123, D4]), ([D4, .s (.H 3)], [.s (.H 3), D4]), ([D4, .s (.Z 3)], [.s (.Z 3), D4])]

theorem T290w_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T290w := by
  intro e he
  simp only [T290w, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact s290 m ih
  · exact qE m 3 (by omega) D4 (by decide) (by decide) _ (Or.inl rfl)
  · exact qE m 3 (by omega) D4 (by decide) (by decide) _ (Or.inr rfl)

theorem run290w : check 4 T290w [D4, Zw] [Zw, D4]
    [.sem 1 1 [.s (.H 3), .s (.Z 3), .s (.H 3), Z123, .s (.H 3), .s (.Z 3), .s (.H 3)] 4,
     .rw 0 1 false, .rw 1 2 false, .rw 2 1 false, .rw 3 0 false, .rw 4 1 false, .rw 5 2 false,
     .rw 6 1 false, .sem 0 7 [Zw] 4] = true := by
  decide +kernel

/-- (290) white on wire `3`. -/
theorem s290w (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [D4, Zw]) (wc 5 (m + 5) [Zw, D4]) :=
  check_sound (frame 4) ih (T290w_ok m ih) run290w

/-! ## (295) and (306) -/

/-- The factors of (295), as in the interface. -/
def F295i : List Lt := [Z123, A2z, D4, A2x, X123, A2z, D4, A2x]

def T295i : SE.Tbl := [([bx0], F295), ([D4, Zw], [Zw, D4])]

theorem T295i_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T295i := by
  intro e he
  simp only [T295i, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s295 m ih
  · exact s290w m ih

theorem run295i : check 4 T295i [bx0] F295i
    [.rw 0 0 false, .sem 0 1 [Z123, Zw] 4, .sem 1 2 [A2z, Zw] 4, .rw 2 1 true,
     .sem 3 2 [A2x, Zw] 4, .sem 4 2 [X123] 4] = true := by
  decide +kernel

/-- (295) on five local wires, as in the interface. -/
theorem s295i (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0]) (wc 5 (m + 5) F295i) :=
  check_sound (frame 4) ih (T295i_ok m ih) run295i

def T306 : SE.Tbl := [([bx0], F295i), ([lS2, D4, lS2], [D4])]

theorem T306_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T306 := by
  intro e he
  simp only [T306, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s295i m ih
  · have h := swE m 2 (by omega) .box [0] [(1, true), (4, true)] true (by decide) (by decide)
    have e : swapG 2 .box [0] [(1, true), (4, true)] true = D4 := by decide
    rw [e] at h
    exact h

theorem run306 : check 4 T306 [bx0, lS2] [lS2, bx0]
    [.rw 0 0 false, .sem 7 2 [lS2, A2x] 4, .sem 6 0 [lS2, lS2] 4, .rw 7 1 false,
     .sem 5 2 [lS2, A2z] 4, .sem 4 2 [lS2, X123] 4, .sem 3 2 [lS2, A2x] 4,
     .sem 2 0 [lS2, lS2] 4, .rw 3 1 false, .sem 1 2 [lS2, A2z] 4, .sem 0 2 [lS2, Z123] 4,
     .rw 1 0 true] = true := by
  decide +kernel

/-- (306) on five local wires: the box commutes with the swap of the wires
`2, 3`. -/
theorem s306 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0, lS2]) (wc 5 (m + 5) [lS2, bx0]) :=
  check_sound (frame 4) ih (T306_ok m ih) run306

/-! ## (292) -/

/-- The box on wire `1`, white on wire `2`, black on `0, 3, 4` and the bulk. -/
def Bw : Lt := .g .box [1] [(0, true), (2, false), (3, true), (4, true)] true
/-- `ZX`, `XZ` on wire `1` controlled by `0` and white on `2`. -/
def Wt : Lt := .g .zx [1] [(0, true), (2, false)] false
def Vt : Lt := .g .xz [1] [(0, true), (2, false)] false

def T269w : SE.Tbl :=
  [(xL 2 ++ [bx0] ++ xL 2, [Bx2w]), ([bx0], [wW, cC, wV, cC]),
   ([cC, .s (.H 2)], [.s (.H 2), cC]), ([cC, .s (.Z 2)], [.s (.Z 2), cC])]

theorem T269w_ok (m : ℕ) : AllD 5 m T269w := by
  intro e he
  simp only [T269w, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact x81_bx0 m
  · exact t269 m
  · exact qE m 2 (by omega) cC (by decide) (by decide) _ (Or.inl rfl)
  · exact qE m 2 (by omega) cC (by decide) (by decide) _ (Or.inr rfl)

theorem run269w : check 4 T269w [Bx2w] [Wb, cC, Vb, cC]
    [.rw 0 0 true, .rw 3 1 false, .sem 0 4 [Wb, .s (.H 2), .s (.Z 2), .s (.H 2)] 4,
     .rw 3 2 true, .rw 2 3 true, .rw 1 2 true, .sem 2 4 [Vb, .s (.H 2), .s (.Z 2), .s (.H 2)] 4,
     .rw 5 2 true, .rw 4 3 true, .rw 3 2 true, .sem 4 6 [] 4] = true := by
  decide +kernel

/-- (269) for the box white on wire `2`. -/
theorem s269w (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Bx2w]) (wc 5 (m + 5) [Wb, cC, Vb, cC]) :=
  check_sound (frame 4) ih (T269w_ok m) run269w

def T269Bw : SE.Tbl :=
  [([Bx2w], [Wb, cC, Vb, cC]), ([lS0, Bx2w, lS0], [Bw]), ([lS0, Wb, lS0], [Wt]),
   ([lS0, cC, lS0], [eA]), ([lS0, Vb, lS0], [Vt])]

theorem T269Bw_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T269Bw := by
  intro e he
  simp only [T269Bw, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact s269w m ih
  all_goals exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)

theorem run269Bw : check 4 T269Bw [Bw] [Wt, eA, Vt, eA]
    [.rw 0 1 true, .rw 1 0 false, .sem 2 0 [lS0, lS0] 4, .sem 5 0 [lS0, lS0] 4,
     .sem 8 0 [lS0, lS0] 4, .rw 0 2 false, .rw 1 3 false, .rw 2 4 false,
     .rw 3 3 false] = true := by
  decide +kernel

/-- (269) for the box `Bw`. -/
theorem s269Bw (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Bw]) (wc 5 (m + 5) [Wt, eA, Vt, eA]) :=
  check_sound (frame 4) ih (T269Bw_ok m ih) run269Bw

def T292 : SE.Tbl := [([Bw], [Wt, eA, Vt, eA]), ([eA, wW], [wW, eA])]

theorem T292_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T292 := by
  intro e he
  simp only [T292, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s269Bw m ih
  · exact s287 m ih

theorem run292 : check 4 T292 [wW, Bw] [Bw, wW]
    [.rw 1 0 false, .sem 0 2 [Wt, wW] 4, .rw 1 1 true, .sem 2 2 [Vt, wW] 4, .rw 3 1 true,
     .rw 0 0 true] = true := by
  decide +kernel

/-- (292) on five local wires. -/
theorem s292 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [wW, Bw]) (wc 5 (m + 5) [Bw, wW]) :=
  check_sound (frame 4) ih (T292_ok m ih) run292

/-! ## (305) -/

def T287w : SE.Tbl :=
  [([eA, wV], [wV, eA]), ([eA, .s (.H 2)], [.s (.H 2), eA]), ([eA, .s (.Z 2)], [.s (.Z 2), eA])]

theorem T287w_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T287w := by
  intro e he
  simp only [T287w, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact s287v m ih
  · exact qE m 2 (by omega) eA (by decide) (by decide) _ (Or.inl rfl)
  · exact qE m 2 (by omega) eA (by decide) (by decide) _ (Or.inr rfl)

theorem run287vw : check 4 T287w [eA, Vb] [Vb, eA]
    [.sem 1 1 [.s (.H 2), .s (.Z 2), .s (.H 2), wV, .s (.H 2), .s (.Z 2), .s (.H 2)] 4,
     .rw 0 1 false, .rw 1 2 false, .rw 2 1 false, .rw 3 0 false, .rw 4 1 false, .rw 5 2 false,
     .rw 6 1 false, .sem 0 7 [Vb] 4] = true := by
  decide +kernel

/-- (287) for `XZ` white on wire `2`. -/
theorem s287vw (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [eA, Vb]) (wc 5 (m + 5) [Vb, eA]) :=
  check_sound (frame 4) ih (T287w_ok m ih) run287vw

def T269f : SE.Tbl :=
  [([bx0], [wW, cC, wV, cC]), ([lS0, bx0, lS0], [bx1p]), ([lS0, wW, lS0], [wW1]),
   ([lS0, cC, lS0], [eA]), ([lS0, wV, lS0], [wV1])]

theorem T269f_ok (m : ℕ) : AllD 5 m T269f := by
  intro e he
  simp only [T269f, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact t269 m
  all_goals exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)

theorem run269f : check 4 T269f [bx1p] [wW1, eA, wV1, eA]
    [.rw 0 1 true, .rw 1 0 false, .sem 2 0 [lS0, lS0] 4, .sem 5 0 [lS0, lS0] 4,
     .sem 8 0 [lS0, lS0] 4, .rw 0 2 false, .rw 1 3 false, .rw 2 4 false,
     .rw 3 3 false] = true := by
  decide +kernel

/-- (269) for the box on wire `1` (all other wires black). -/
theorem s269f (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx1p]) (wc 5 (m + 5) [wW1, eA, wV1, eA]) :=
  check_sound (frame 4) ih (T269f_ok m) run269f

def TVbBf : SE.Tbl := [([bx1p], [wW1, eA, wV1, eA]), ([eA, Vb], [Vb, eA])]

theorem TVbBf_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TVbBf := by
  intro e he
  simp only [TVbBf, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact s269f m ih
  · exact s287vw m ih

theorem runVbBf : check 4 TVbBf [Vb, bx1p] [bx1p, Vb]
    [.rw 1 0 false, .sem 0 2 [wW1, Vb] 4, .rw 1 1 true, .sem 2 2 [wV1, Vb] 4, .rw 3 1 true,
     .rw 0 0 true] = true := by
  decide +kernel

/-- `XZ` on wire `0` controlled by `1` and white on `2` passes the box on
wire `1`. -/
theorem sVbBf (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Vb, bx1p]) (wc 5 (m + 5) [bx1p, Vb]) :=
  check_sound (frame 4) ih (TVbBf_ok m ih) runVbBf

def TBw2 : SE.Tbl :=
  [([lS0, Bx2w, lS0], [Bw]), (xL 2 ++ [bx0] ++ xL 2, [Bx2w]), ([bx0, bx0], [])]

theorem TBw2_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m TBw2 := by
  intro e he
  simp only [TBw2, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
  · exact x81_bx0 m
  · exact s299 m ih

theorem runBw2 : check 4 TBw2 [Bw, Bw] []
    [.rw 0 0 true, .rw 3 0 true, .sem 2 2 [] 4, .rw 1 1 true, .rw 8 1 true, .sem 5 6 [] 4,
     .rw 4 2 false, .sem 1 6 [] 4, .sem 0 2 [] 4] = true := by
  decide +kernel

/-- The box `Bw` is an involution. -/
theorem sBw2 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Bw, Bw]) (wc 5 (m + 5) []) :=
  check_sound (frame 4) ih (TBw2_ok m ih) runBw2

def T301r : SE.Tbl :=
  [([lS0, bx0, lS0], [bx1p]), ([lS0, Bx2w, lS0], [Bw]), ([bx0, Bx2w], [eA]), ([lS0, eA, lS0], [cC])]

theorem T301r_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T301r := by
  intro e he
  simp only [T301r, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
  · exact s301 m ih
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)

theorem run301r : check 4 T301r [bx1p, Bw] [cC]
    [.rw 0 0 true, .rw 3 1 true, .sem 2 2 [] 4, .rw 1 2 false, .rw 0 3 false] = true := by
  decide +kernel

/-- (301) relabeled by the swap of the wires `0, 1`. -/
theorem s301r (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx1p, Bw]) (wc 5 (m + 5) [cC]) :=
  check_sound (frame 4) ih (T301r_ok m ih) run301r

def T302r : SE.Tbl :=
  [([lS0, bx0, lS0], [bx1p]), ([lS0, Bx2w, lS0], [Bw]), ([Bx2w, bx0], [eA]), ([lS0, eA, lS0], [cC])]

theorem T302r_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T302r := by
  intro e he
  simp only [T302r, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
  · exact s302 m ih
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)

theorem run302r : check 4 T302r [Bw, bx1p] [cC]
    [.rw 0 1 true, .rw 3 0 true, .sem 2 2 [] 4, .rw 1 2 false, .rw 0 3 false] = true := by
  decide +kernel

/-- (302) relabeled by the swap of the wires `0, 1`. -/
theorem s302r (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Bw, bx1p]) (wc 5 (m + 5) [cC]) :=
  check_sound (frame 4) ih (T302r_ok m ih) run302r

/-- `XZ` on wire `0` controlled by wire `1`. -/
def V1 : Lt := .g .xz [0] [(1, true)] false

def T305 : SE.Tbl :=
  [([Vb, bx1p], [bx1p, Vb]), ([Bw, Bw], []), ([wW, Bw], [Bw, wW]), ([bx1p, Bw], [cC]),
   ([Bw, bx1p], [cC]), ([bx0], [wV, cC, wW, cC])]

theorem T305_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T305 := by
  intro e he
  simp only [T305, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sVbBf m ih
  · exact sBw2 m ih
  · exact s292 m ih
  · exact s301r m ih
  · exact s302r m ih
  · exact s286 m ih

theorem run305 : check 4 T305 [V1, bx1p, W1, bx1p] [bx0]
    [.sem 0 1 [wV, Vb] 4, .sem 3 1 [Wb, wW] 4, .rw 1 0 false, .sem 2 2 [] 4, .rw 2 1 true,
     .rw 3 2 true, .rw 1 3 false, .rw 3 4 false, .rw 0 5 true] = true := by
  decide +kernel

/-- (305) on five local wires. -/
theorem s305 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [V1, bx1p, W1, bx1p]) (wc 5 (m + 5) [bx0]) :=
  check_sound (frame 4) ih (T305_ok m ih) run305

end QCert.RealCliffordCH.Sec8.D.N8
