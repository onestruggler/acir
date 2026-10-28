/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The statements of package (iv) on three wires

On three wires the box with two controls is `CZ` of the wires `1, 2`, and
the equations come from Lemma D.2 at width 3 (`Small.eqNNN 0`, proved in
`W3`) and two-wire semantic steps, by the engine `SymEngine` on three local
wires without bulk (`frame 2`):

* (300) (`t300`): (126) is (269) on three wires, and `C W C V` is its
  inverse ((117), (118), the box an involution);
* (292) (`t292`): the white `CZ` of the wires `0, 2` is `Z0` times the
  black one, which pass `W` by (125) and (128);
* (305) (`t305`): `ZX(0 | 1)` and `XZ(0 | 1)` split by (136), (138); the
  white halves pass the `CZ` of the wires `0, 2` ((125), (128) conjugated by
  `X` on wire `2`, `tcWb`) and cancel ((118)); the black ones are (128).

The letters on three wires are the gates of the interface on the nose, and
so are the multi-controlled ones, by unfolding (`Net.der_of_eq`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.D9

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

abbrev lC1 : Lt := .s (.C 1)
abbrev lZ1 : Lt := .s (.Z 1)

/-- `ZX`, `XZ` of the wires `1, 2` onto wire `0` (Definition 2.4), as letters. -/
def zxw : List Lt := [lK0, lS0, lC1, lS0, lK0, lS0, lC1, lS0]
def xzw : List Lt := [lS0, lC1, lS0, lK0, lS0, lC1, lS0, lK0]
/-- `CZ` of the wires `0, 2`. -/
def cL : List Lt := [lS0, lC1, lS0]
/-- `ZX(0 | 1)`, `XZ(0 | 1)` as letters. -/
def W1s : List Lt := [lK0, lS0, lZ1, lS0, lK0, lS0, lZ1, lS0]
def V1s : List Lt := [lS0, lZ1, lS0, lK0, lS0, lZ1, lS0, lK0]

def W3 : Lt := .g .zx [0] [(1, true), (2, true)] false
def V3 : Lt := .g .xz [0] [(1, true), (2, true)] false
def B3 : Lt := .g .box [0] [(1, true), (2, true)] false
def C3 : Lt := .g .box [1] [(0, true)] false
def Bp3 : Lt := .g .box [1] [(0, true), (2, true)] false
def Bw3 : Lt := .g .box [1] [(0, true), (2, false)] false
def W1p : Lt := .g .zx [0] [(1, true)] false
def V1p : Lt := .g .xz [0] [(1, true)] false

/-- A fixed-width equation of `Small` as a table entry on three local wires. -/
theorem smallE {l r : List L} {lc rc : Circ 3} (hl : lc = circW 3 l) (hr : rc = circW 3 r)
    (h : Derivable (theory (0 + 3)) (Circuit.pad 0 lc) (Circuit.pad 0 rc)) :
    Derivable (theory (0 + 2 + 1)) (wc 3 (0 + 2 + 1) (l.map Lt.s)) (wc 3 (0 + 2 + 1) (r.map Lt.s)) := by
  rw [pad_zero3, pad_zero3, hl, hr] at h
  have e : ∀ l : List L, wc 3 3 (l.map Lt.s) = circW 3 l := by
    intro l; simp [wc, circW, List.map_map, Function.comp_def, Lt.circ]
  rw [show (0 + 2 + 1) = 3 from rfl, e, e]
  exact h

/-- The table of the three-wire runs. -/
def T3 : SE.Tbl :=
  [([W3], zxw), ([V3], xzw), ([B3], [lC1]), ([Bp3], cL), ([W1p], W1s), ([V1p], V1s),
   (zxw ++ xzw, []), (xzw ++ zxw, []), ([lZ0] ++ zxw, zxw ++ [lZ0, lC1]),
   (zxw ++ [lZ0] ++ xzw ++ [lZ0], [lC1]), (cL ++ zxw, zxw ++ [lC1] ++ cL),
   (xL 2 ++ zxw ++ xL 2 ++ zxw, W1s), (xzw ++ xL 2 ++ xzw ++ xL 2, V1s), (xL 2 ++ [Bp3] ++ xL 2, [Bw3])]

set_option maxRecDepth 100000 in
theorem T3_ok (ih : IH 3) : AllD 3 0 T3 := by
  intro e he
  simp only [T3, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact der_of_eq (by rfl)
  · exact der_of_eq (by rfl)
  · exact der_of_eq (by rfl)
  · exact der_of_eq (by rfl)
  · exact der_of_eq (by rfl)
  · exact der_of_eq (by rfl)
  · exact smallE (l := [.K 0, .S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .S 0, .C 1, .S 0, .K 0,
      .S 0, .C 1, .S 0, .K 0]) (r := []) rfl rfl (eq117 0 ih)
  · exact smallE (l := [.S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .K 0, .K 0, .S 0, .C 1, .S 0,
      .K 0, .S 0, .C 1, .S 0]) (r := []) rfl rfl (eq118 0 ih)
  · exact smallE (l := [.Z 0, .K 0, .S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0])
      (r := [.K 0, .S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .Z 0, .C 1]) rfl rfl (eq125 0 ih)
  · exact smallE (l := [.K 0, .S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .Z 0, .S 0, .C 1, .S 0,
      .K 0, .S 0, .C 1, .S 0, .K 0, .Z 0]) (r := [.C 1]) rfl rfl (eq126 0 ih)
  · exact smallE (l := [.S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0])
      (r := [.K 0, .S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .C 1, .S 0, .C 1, .S 0]) rfl rfl
      (eq128 0 ih)
  · exact smallE (l := [.H 2, .Z 2, .H 2, .K 0, .S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .H 2,
      .Z 2, .H 2, .K 0, .S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0])
      (r := [.K 0, .S 0, .Z 1, .S 0, .K 0, .S 0, .Z 1, .S 0]) rfl rfl (eq136 0 ih)
  · exact smallE (l := [.S 0, .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .K 0, .H 2, .Z 2, .H 2, .S 0,
      .C 1, .S 0, .K 0, .S 0, .C 1, .S 0, .K 0, .H 2, .Z 2, .H 2])
      (r := [.S 0, .Z 1, .S 0, .K 0, .S 0, .Z 1, .S 0, .K 0]) rfl rfl (eq138 0 ih)
  · exact x81E 0 3 2 (by omega) .box [1] _ _ false true (by decide) (by decide) (by decide)

theorem run300_3 : check 2 T3 [B3] [C3, W3, C3, V3]
    [.rw 0 2 false, .sem 0 0 [lZ0, lZ0] 2, .rw 1 6 true, .sem 9 0 [lZ0, lZ0] 2, .rw 10 7 true,
     .rw 18 9 false, .sem 18 2 [] 0, .rw 1 0 true, .rw 3 1 true, .sem 0 1 [C3] 2,
     .sem 2 1 [C3] 2] = true := by
  decide +kernel

/-- (300) on three wires. -/
theorem t300 (ih : IH 3) :
    Derivable (theory 3) (wc 3 3 [B3]) (wc 3 3 [C3, W3, C3, V3]) :=
  check_sound (frame 2) (m := 0) ih (T3_ok ih) run300_3

theorem run292_3 : check 2 T3 [W3, Bw3] [Bw3, W3]
    [.rw 0 0 false, .rw 8 13 true, .rw 11 3 false, .sw 10, .sw 9, .sw 8, .sw 13, .sw 14, .sw 15,
     .sem 9 7 [lZ1, lC1] 0, .sem 10 0 [lS0, lS0] 2, .sem 8 3 [lZ0] 2, .sem 9 0 [lC1, lC1] 0,
     .rw 0 8 true, .rw 1 10 true, .rw 4 0 true, .sem 0 1 [lS0, lZ1, lS0] 2, .sem 2 2 [] 2,
     .sem 1 2 [.s (.H 2), .s (.Z 2), .s (.H 2), lC1, .s (.H 2), .s (.Z 2), .s (.H 2)] 0,
     .sw 0, .sw 1, .sw 2, .sw 7, .sw 6, .sw 5, .rw 3 3 true, .rw 0 13 false] = true := by
  decide +kernel

/-- (292) on three wires. -/
theorem t292 (ih : IH 3) : Derivable (theory 3) (wc 3 3 [W3, Bw3]) (wc 3 3 [Bw3, W3]) :=
  check_sound (frame 2) (m := 0) ih (T3_ok ih) run292_3

theorem runcWb : check 2 T3 (cL ++ xL 2 ++ zxw ++ xL 2) (xL 2 ++ zxw ++ xL 2 ++ cL)
    [.sem 0 0 [.s (.H 2), .s (.Z 2), .s (.H 2), .s (.H 2), .s (.Z 2), .s (.H 2)] 1,
     .sw 5, .sw 4, .sw 3, .sw 8, .sw 9, .sw 10, .sem 4 7 [lZ1, lC1] 0, .sem 5 0 [lS0, lS0] 2,
     .sem 3 3 [lZ0] 2, .rw 4 10 false, .rw 3 8 false, .sem 12 2 [] 0,
     .sem 11 1 [lS0, lZ1, lS0] 2, .sem 13 2 [] 2,
     .sem 12 2 [.s (.H 2), .s (.Z 2), .s (.H 2), lC1, .s (.H 2), .s (.Z 2), .s (.H 2)] 0,
     .sw 11, .sw 12, .sw 13, .sw 18, .sw 17, .sw 16, .sem 17 6 [] 1] = true := by
  decide +kernel

theorem tcWb (ih : IH 3) :
    Derivable (theory 3) (wc 3 3 (cL ++ xL 2 ++ zxw ++ xL 2)) (wc 3 3 (xL 2 ++ zxw ++ xL 2 ++ cL)) :=
  check_sound (frame 2) (m := 0) ih (T3_ok ih) runcWb

def T305_3 : SE.Tbl := T3 ++ [(cL ++ xL 2 ++ zxw ++ xL 2, xL 2 ++ zxw ++ xL 2 ++ cL)]

theorem T305_3_ok (ih : IH 3) : AllD 3 0 T305_3 := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact T3_ok ih e he
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl
    exact tcWb ih

theorem run305_3 : check 2 T305_3 [V1p, Bp3, W1p, Bp3] [B3]
    [.rw 0 5 false, .rw 8 3 false, .rw 11 4 false, .rw 19 3 false, .rw 0 12 true, .rw 25 11 true,
     .rw 22 14 false, .sem 19 6 [] 1, .rw 11 7 false, .sem 8 6 [] 1, .rw 8 10 false,
     .sem 19 2 [] 2, .sem 18 2 [] 0, .sem 17 2 [] 2, .rw 0 7 false, .rw 0 2 true] = true := by
  decide +kernel

/-- (305) on three wires. -/
theorem t305 (ih : IH 3) :
    Derivable (theory 3) (wc 3 3 [V1p, Bp3, W1p, Bp3]) (wc 3 3 [B3]) :=
  check_sound (frame 2) (m := 0) ih (T305_3_ok ih) run305_3

end QCert.RealCliffordCH.Sec8.D.N8
