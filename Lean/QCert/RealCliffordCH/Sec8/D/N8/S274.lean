/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (272) and (274) at every width

On five local wires (wires `0, …, 4`, the bulk above).  The paper's proof of
(272) applies (19) and (269) to the box whose box wire is wire `2`; here
these are carried there from `Anchors` by the swaps of the wires `0, 1` and
`1, 2` (`r19b`, `r269b`, by `Net.mc_swap`).  The relabeling moves the inner
box of (269) to `B0` (box wire `0`, wire `1` idle), so (272) is proved for
`B0` (`s272`), and (274), `B1 = B0`, follows by writing the swap of the wires
`0, 1` as Equation (8) and passing `B0` through it (`s274`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.Anchors

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

def bx1p : Lt := swapG 0 .box [0] [(1, true), (2, true), (3, true), (4, true)] true
/-- The box on wire `2`, all other wires black. -/
def bx2 : Lt := swapG 1 .box [1] [(0, true), (2, true), (3, true), (4, true)] true
def wW1 : Lt := swapG 0 .zx [0] [(1, true), (2, true)] false
def zx2l : Lt := swapG 1 .zx [1] [(0, true), (2, true)] false
def wV1 : Lt := swapG 0 .xz [0] [(1, true), (2, true)] false
def xz2l : Lt := swapG 1 .xz [1] [(0, true), (2, true)] false
def cC1 : Lt := swapG 0 .box [1] [(0, true), (3, true), (4, true)] true
/-- The box on wire `0`, controls `2, 3, 4` and the bulk, wire `1` idle. -/
def B0 : Lt := swapG 1 .box [0] [(1, true), (3, true), (4, true)] true
/-- The box on wire `1`, controls `2, 3, 4` and the bulk, wire `0` idle. -/
def B1 : Lt := swapG 0 .box [0] [(2, true), (3, true), (4, true)] true

theorem bx0_eq : bx0 = .g .box [0] [(1, true), (2, true), (3, true), (4, true)] true := rfl
theorem bx2_eq : bx2 = .g .box [2] [(0, true), (1, true), (3, true), (4, true)] true := by decide
theorem B0_eq : B0 = .g .box [0] [(2, true), (3, true), (4, true)] true := by decide
theorem B1_eq : B1 = .g .box [1] [(2, true), (3, true), (4, true)] true := by decide

/-- A table entry from `swapE`. -/
theorem swE (m j : ℕ) (hj : j + 2 ≤ 5) (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool)) (b : Bool)
    (hx : (Lt.g Kd tg cs b).ok 5 = true)
    (hnc : ¬ ((cs.lookup j).isSome = true ∧ j ∉ tg ∧ (cs.lookup (j + 1)).isSome = true ∧
      j + 1 ∉ tg)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [.s (.S j), .g Kd tg cs b, .s (.S j)])
      (wc 5 (m + 5) [swapG j Kd tg cs b]) :=
  swapE m 5 j hj Kd tg cs b hx hnc

/-! ## (19) and (269) for the box on wire `2` -/

def T19b : SE.Tbl :=
  [([.s (.Z 0), bx0], [bx0, .s (.Z 0)]),
   ([.s (.S 0), bx0, .s (.S 0)], [bx1p]),
   ([.s (.S 1), bx1p, .s (.S 1)], [bx2])]

theorem T19b_ok (m : ℕ) : AllD 5 m T19b := by
  intro e he
  simp only [T19b, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact t19 m
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
  · exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)

theorem run19b : check 4 T19b [.s (.Z 2), bx2] [bx2, .s (.Z 2)]
    [.rw 1 2 true, .rw 2 1 true, .sem 0 3 [.s (.S 1), .s (.S 0), .s (.Z 0)] 4, .rw 2 0 false,
     .sem 3 3 [.s (.S 0), .s (.S 1), .s (.Z 2)] 4, .rw 1 1 false, .rw 0 2 false] = true := by
  decide +kernel

/-- (19) for the box on wire `2`. -/
theorem r19b (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [.s (.Z 2), bx2]) (wc 5 (m + 5) [bx2, .s (.Z 2)]) :=
  check_sound (frame 4) ih (T19b_ok m) run19b

def T269b : SE.Tbl :=
  [([bx0], [wW, cC, wV, cC]),
   ([.s (.S 0), bx0, .s (.S 0)], [bx1p]),
   ([.s (.S 1), bx1p, .s (.S 1)], [bx2]),
   ([.s (.S 0), wW, .s (.S 0)], [wW1]),
   ([.s (.S 1), wW1, .s (.S 1)], [zx2l]),
   ([.s (.S 0), cC, .s (.S 0)], [cC1]),
   ([.s (.S 1), cC1, .s (.S 1)], [B0]),
   ([.s (.S 0), wV, .s (.S 0)], [wV1]),
   ([.s (.S 1), wV1, .s (.S 1)], [xz2l])]

theorem T269b_ok (m : ℕ) : AllD 5 m T269b := by
  intro e he
  simp only [T269b, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact t269 m
  all_goals first
    | exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
    | exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)

def ins01 : List Lt := [.s (.S 0), .s (.S 1), .s (.S 1), .s (.S 0)]

theorem run269b : check 4 T269b [bx2] [zx2l, B0, xz2l, B0]
    [.rw 0 2 true, .rw 1 1 true, .rw 2 0 false,
     .sem 3 0 ins01 4, .sem 8 0 ins01 4, .sem 13 0 ins01 4,
     .rw 16 5 false, .rw 15 6 false, .rw 11 7 false, .rw 10 8 false,
     .rw 6 5 false, .rw 5 6 false, .rw 1 3 false, .rw 0 4 false] = true := by
  decide +kernel

/-- (269) for the box on wire `2`. -/
theorem r269b (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx2]) (wc 5 (m + 5) [zx2l, B0, xz2l, B0]) :=
  check_sound (frame 4) ih (T269b_ok m) run269b

/-! ## (272) -/

def T272 : SE.Tbl := [([.s (.Z 2), bx2], [bx2, .s (.Z 2)]), ([bx2], [zx2l, B0, xz2l, B0])]

theorem T272_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T272 := by
  intro e he
  simp only [T272, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact r19b m ih
  · exact r269b m ih

theorem run272 : check 4 T272 [.s (.C 0), B0] [B0, .s (.C 0)]
    [.sem 0 1 [.s (.Z 2), xz2l, zx2l, .s (.Z 2), .s (.C 0)] 4,
     .sem 6 0 [xz2l, zx2l] 4,
     .sem 7 0 [B0, B0] 1,
     .sem 2 3 [.s (.Z 2), zx2l] 4,
     .rw 3 1 true, .rw 2 0 false, .rw 2 1 false,
     .sem 5 3 [.s (.Z 2)] 1,
     .sem 0 3 [.s (.Z 2)] 4,
     .sem 2 3 [.s (.Z 2), .s (.C 0)] 4,
     .sem 0 3 [B0] 1] = true := by
  decide +kernel

/-- (272), with the box `B0`: `CZ` of the wires `0, 1` commutes with the box
on wire `0` (controls `2, 3, 4` and the bulk, wire `1` idle). -/
theorem s272 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [.s (.C 0), B0]) (wc 5 (m + 5) [B0, .s (.C 0)]) :=
  check_sound (frame 4) ih (T272_ok m ih) run272

/-! ## (274) -/

def T274 : SE.Tbl :=
  [([.s (.C 0), B0], [B0, .s (.C 0)]),
   ([B0, .s (.H 1)], [.s (.H 1), B0]),
   ([.s (.S 0), B0, .s (.S 0)], [B1])]

theorem T274_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T274 := by
  intro e he
  simp only [T274, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact s272 m ih
  · exact qcommE m 4 1 (by omega) B0 (by decide) (by decide) (.H 1) (Or.inl rfl)
  · exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)

def sw9 : List Lt := [.s (.C 0), .s (.H 1), .s (.H 0), .s (.C 0), .s (.H 1), .s (.H 0),
  .s (.C 0), .s (.H 1), .s (.H 0)]

theorem run274 : check 4 T274 [B1] [B0]
    [.rw 0 2 true, .sem 2 1 sw9 2,
     .rw 1 0 true, .rw 2 1 false, .sem 3 2 [.s (.H 0), B0] 1,
     .rw 4 0 true, .rw 5 1 false, .sem 6 2 [.s (.H 0), B0] 1,
     .rw 7 0 true, .rw 8 1 false, .sem 9 2 [.s (.H 0), B0] 1,
     .sem 1 9 [.s (.S 0)] 2, .sem 0 2 [] 2] = true := by
  decide +kernel

/-- (274) on five local wires: the box wire is an identity wire. -/
theorem s274 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [B1]) (wc 5 (m + 5) [B0]) :=
  check_sound (frame 4) ih (T274_ok m ih) run274

end QCert.RealCliffordCH.Sec8.D.N8
