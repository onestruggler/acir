/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (287) and (300)–(302) at every width from five

On five local wires, with `bx0 = W C V C` of (269) and `bx0² = 1` ((299),
`S299.s299`).

* (287), the box `eA` (box wire `0`, controls `1, 3, 4` and the bulk, wire
  `2` idle) passes `W = ZX(0 | 1, 2)` and `V = XZ(0 | 1, 2)` (`s287`, `s287v`):
  `W` is `t c t c` with `t` the `CH` from wire `1` onto wire `0` and `c` the
  `CZ` of the wires `0, 2`; `eA` passes `t` by Lemma 5.1 and `c` by (272)
  relabeled (`S285.sL2`).  The paper's proof.
* (300), `bx0 = C W C V` (`s300`): `C W C V` is the inverse of `W C V C`, which
  is `bx0`, an involution.
* (300) for the box white on wire `2` (`s300w`), through (81) (`Kit.x81E`).
* (301), the box followed by its version white on wire `2` is the box without
  a control on wire `2` (`s301`): with (269) and (300) the product is
  `W C V Ṽ C V̄`, `Ṽ`, `V̄` the white versions; `V W̄` is `c ZX(0 | 1) c`, `c`
  passes `C` ((271), `S275.s271c`), `C ZX(0 | 1) C` is `ZX(0 | 1)` times
  `eA` (Lemma 5.1), `eA` passes `c` ((272)) and `W` ((287)), and what is left
  is the identity on four wires (Lemma 5.1).  Not the paper's route, which
  goes through Equations (141)–(143).
* (302), the other order (`s302`): (301) conjugated by `X` on wire `2`.
-/
import QCert.RealCliffordCH.Sec8.D.N8.S299
import QCert.RealCliffordCH.Sec8.D.N8.Kit

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

/-! ## (287) -/

def T287 : SE.Tbl := [([c3, eA], [eA, c3])]

theorem T287_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T287 := by
  intro e he
  simp only [T287, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl
  exact sL2 m ih

theorem run287 : check 4 T287 [eA, wW] [wW, eA]
    [.sem 1 1 [lK0, c3, lK0, c3] 4, .sem 0 2 [lK0, eA] 2, .rw 1 0 true, .sem 2 2 [lK0, eA] 2,
     .rw 3 0 true, .sem 0 4 [wW] 4] = true := by
  decide +kernel

/-- (287) on five local wires. -/
theorem s287 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [eA, wW]) (wc 5 (m + 5) [wW, eA]) :=
  check_sound (frame 4) ih (T287_ok m ih) run287

theorem run287v : check 4 T287 [eA, wV] [wV, eA]
    [.sem 1 1 [c3, lK0, c3, lK0] 4, .rw 0 0 true, .sem 1 2 [lK0, eA] 2, .rw 2 0 true,
     .sem 3 2 [lK0, eA] 2, .sem 0 4 [wV] 4] = true := by
  decide +kernel

/-- (287) for `XZ` on five local wires. -/
theorem s287v (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [eA, wV]) (wc 5 (m + 5) [wV, eA]) :=
  check_sound (frame 4) ih (T287_ok m ih) run287v

/-! ## (300) -/

def T300 : SE.Tbl := [([bx0], [wW, cC, wV, cC]), ([bx0, bx0], [])]

theorem T300_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T300 := by
  intro e he
  simp only [T300, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact t269 m
  · exact s299 m ih

theorem run300 : check 4 T300 [bx0] [cC, wW, cC, wV]
    [.sem 0 0 [cC, cC] 2, .sem 1 0 [wW, wV] 4, .sem 2 0 [cC, cC] 2, .sem 3 0 [wV, wW] 4,
     .rw 4 0 true, .rw 4 1 false] = true := by
  decide +kernel

/-- (300) on five local wires. -/
theorem s300 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0]) (wc 5 (m + 5) [cC, wW, cC, wV]) :=
  check_sound (frame 4) ih (T300_ok m ih) run300

/-! ## (300) with a white control on wire `2` -/

/-- The box white on wire `2`. -/
def Bx2w : Lt := .g .box [0] [(1, true), (2, false), (3, true), (4, true)] true
/-- `W`, `V` white on wire `2`. -/
def Wb : Lt := .g .zx [0] [(1, true), (2, false)] false
def Vb : Lt := .g .xz [0] [(1, true), (2, false)] false

theorem x81_bx0 (m : ℕ) : Derivable (theory (m + 5)) (wc 5 (m + 5) (xL 2 ++ [bx0] ++ xL 2))
    (wc 5 (m + 5) [Bx2w]) :=
  x81E m 5 2 (by omega) .box [0] _ _ true true (by decide) (by decide) (by decide)

theorem x81_Bx2w (m : ℕ) : Derivable (theory (m + 5)) (wc 5 (m + 5) (xL 2 ++ [Bx2w] ++ xL 2))
    (wc 5 (m + 5) [bx0]) :=
  x81E m 5 2 (by omega) .box [0] _ _ true false (by decide) (by decide) (by decide)

def T300w : SE.Tbl :=
  [(xL 2 ++ [bx0] ++ xL 2, [Bx2w]), ([bx0], [cC, wW, cC, wV]),
   ([cC, .s (.H 2)], [.s (.H 2), cC]), ([cC, .s (.Z 2)], [.s (.Z 2), cC])]

theorem T300w_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T300w := by
  intro e he
  simp only [T300w, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact x81_bx0 m
  · exact s300 m ih
  · exact qE m 2 (by omega) cC (by decide) (by decide) _ (Or.inl rfl)
  · exact qE m 2 (by omega) cC (by decide) (by decide) _ (Or.inr rfl)

theorem run300w : check 4 T300w [Bx2w] [cC, Wb, cC, Vb]
    [.rw 0 0 true, .rw 3 1 false, .rw 2 2 true, .rw 1 3 true, .rw 0 2 true,
     .sem 1 4 [Wb, .s (.H 2), .s (.Z 2), .s (.H 2)] 4, .rw 4 2 true, .rw 3 3 true, .rw 2 2 true,
     .sem 3 7 [Vb] 4] = true := by
  decide +kernel

/-- (300) for the box white on wire `2`, on five local wires. -/
theorem s300w (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Bx2w]) (wc 5 (m + 5) [cC, Wb, cC, Vb]) :=
  check_sound (frame 4) ih (T300w_ok m ih) run300w

/-! ## (301) and (302) -/

/-- `ZX` on wire `0` controlled by wire `1`. -/
def W1 : Lt := .g .zx [0] [(1, true)] false

def T301 : SE.Tbl :=
  [([bx0], [wW, cC, wV, cC]), ([Bx2w], [cC, Wb, cC, Vb]), (cz02L ++ [cC], [cC] ++ cz02L),
   ([c3, eA], [eA, c3]), ([eA, wW], [wW, eA])]

theorem T301_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T301 := by
  intro e he
  simp only [T301, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact t269 m
  · exact s300w m ih
  · exact s271c m ih
  · exact sL2 m ih
  · exact s287 m ih

theorem run301 : check 4 T301 [bx0, Bx2w] [eA]
    [.rw 0 0 false, .rw 4 1 false, .sem 3 2 [] 2,
     .sem 2 2 [lS1, lC0, lS1, W1, lS1, lC0, lS1] 4, .rw 1 2 true, .rw 6 2 false,
     .sem 4 3 [eA, W1] 2, .sem 1 3 [c3] 4, .rw 1 3 false, .rw 0 4 true,
     .sem 1 7 [] 4] = true := by
  decide +kernel

/-- (301) on five local wires: the box followed by its version white on wire
`2` is the box without a control on wire `2`. -/
theorem s301 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0, Bx2w]) (wc 5 (m + 5) [eA]) :=
  check_sound (frame 4) ih (T301_ok m ih) run301

def T302 : SE.Tbl :=
  [(xL 2 ++ [bx0] ++ xL 2, [Bx2w]), (xL 2 ++ [Bx2w] ++ xL 2, [bx0]), ([bx0, Bx2w], [eA]),
   ([eA, .s (.H 2)], [.s (.H 2), eA]), ([eA, .s (.Z 2)], [.s (.Z 2), eA])]

theorem T302_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T302 := by
  intro e he
  simp only [T302, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact x81_bx0 m
  · exact x81_Bx2w m
  · exact s301 m ih
  · exact qE m 2 (by omega) eA (by decide) (by decide) _ (Or.inl rfl)
  · exact qE m 2 (by omega) eA (by decide) (by decide) _ (Or.inr rfl)

theorem run302 : check 4 T302 [Bx2w, bx0] [eA]
    [.rw 0 0 true, .rw 7 1 true, .sem 4 6 [] 0, .rw 3 2 false, .rw 2 3 true, .rw 1 4 true,
     .rw 0 3 true, .sem 1 6 [] 0] = true := by
  decide +kernel

/-- (302) on five local wires. -/
theorem s302 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Bx2w, bx0]) (wc 5 (m + 5) [eA]) :=
  check_sound (frame 4) ih (T302_ok m ih) run302

end QCert.RealCliffordCH.Sec8.D.N8
