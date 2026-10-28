/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (286), (273) and (275) at every width

On five local wires, with the box `bx0 = W C V C` of (269).

* (286), `bx0 = V C W C`: (19) conjugated by `Z` on wire `0`, which
  exchanges `W` and `V` and passes `C` (`s286`).
* (273), `CZ` of the wires `0, 2` commutes with `bx0`: it exchanges `W` and
  `V` and passes `C` (`s271c`, a chain of semantic steps as for (271)), so it
  carries `W C V C` to `V C W C`, which is `bx0` by (286) (`s273`).  The
  paper's proof goes through (271) and (272) instead.
* (275), the swap of the wires `1, 2` commutes with `bx0`: it fixes `W` and
  `V` and carries `C` to the box on wire `2`, which is `C` again by (274)
  under a relabeling of the wires (`s274r`, `s275`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.S274

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

/-! ## (286) -/

def T286 : SE.Tbl := [([.s (.Z 0), bx0], [bx0, .s (.Z 0)]), ([bx0], [wW, cC, wV, cC])]

theorem T286_ok (m : ℕ) : AllD 5 m T286 := by
  intro e he
  simp only [T286, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact t19 m
  · exact t269 m

theorem run286 : check 4 T286 [bx0] [wV, cC, wW, cC]
    [.sem 0 0 [.s (.Z 0), .s (.Z 0)] 4, .rw 1 0 false, .rw 1 1 false,
     .sem 0 2 [wV, .s (.Z 0)] 4, .sem 1 2 [cC, .s (.Z 0)] 2, .sem 2 2 [wW, .s (.Z 0)] 4,
     .sem 3 3 [cC] 2] = true := by
  decide +kernel

/-- (286) on five local wires: the box is `V C W C`. -/
theorem s286 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0]) (wc 5 (m + 5) [wV, cC, wW, cC]) :=
  check_sound (frame 4) ih (T286_ok m) run286

/-! ## (273) -/

/-- `CZ` of the wires `0, 2`. -/
def cz02L : List Lt := [.s (.S 1), .s (.C 0), .s (.S 1)]
def zxB : Lt := .g .zx [1] [(0, true), (3, true)] false
def xzB : Lt := .g .xz [1] [(0, true), (3, true)] false
def bB : Lt := .g .box [0] [(1, true), (4, true)] true

theorem run271c : check 4 [] (cz02L ++ [cC]) ([cC] ++ cz02L)
    [.sem 3 1 [zxB, bB, xzB, bB] 2,
     .sem 0 4 ([zxB] ++ cz02L) 4, .sem 1 4 ([bB] ++ cz02L) 3,
     .sem 2 4 ([xzB] ++ cz02L) 4, .sem 3 4 ([bB] ++ cz02L) 3,
     .sem 0 4 [cC] 2] = true := by
  decide +kernel

/-- `CZ` of the wires `0, 2` commutes with the inner box of (269). -/
theorem s271c (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) (cz02L ++ [cC])) (wc 5 (m + 5) ([cC] ++ cz02L)) :=
  check_sound (frame 4) ih (T := []) (fun _ h => by simp at h) run271c

def T273 : SE.Tbl :=
  [([bx0], [wW, cC, wV, cC]), (cz02L ++ [cC], [cC] ++ cz02L), ([bx0], [wV, cC, wW, cC])]

theorem T273_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T273 := by
  intro e he
  simp only [T273, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact t269 m
  · exact s271c m ih
  · exact s286 m ih

theorem run273 : check 4 T273 (cz02L ++ [bx0]) ([bx0] ++ cz02L)
    [.rw 3 0 false, .sem 0 4 ([wV] ++ cz02L) 4, .rw 1 1 false, .sem 2 4 ([wW] ++ cz02L) 4,
     .rw 3 1 false, .rw 0 2 true] = true := by
  decide +kernel

/-- (273) on five local wires: `CZ` of the box wire and the control `2`
commutes with the box. -/
theorem s273 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) (cz02L ++ [bx0])) (wc 5 (m + 5) ([bx0] ++ cz02L)) :=
  check_sound (frame 4) ih (T273_ok m ih) run273

/-! ## (275) -/

def a1 : Lt := swapG 1 .box [1] [(2, true), (3, true), (4, true)] true
def a2 : Lt := swapG 0 .box [2] [(1, true), (3, true), (4, true)] true
def b1 : Lt := swapG 1 .box [0] [(2, true), (3, true), (4, true)] true
def b2 : Lt := swapG 0 .box [0] [(1, true), (3, true), (4, true)] true

def T274r : SE.Tbl :=
  [([B1], [B0]),
   ([.s (.S 1), B1, .s (.S 1)], [a1]),
   ([.s (.S 0), a1, .s (.S 0)], [a2]),
   ([.s (.S 1), B0, .s (.S 1)], [b1]),
   ([.s (.S 0), b1, .s (.S 0)], [b2])]

theorem T274r_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T274r := by
  intro e he
  simp only [T274r, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact s274 m ih
  all_goals first
    | exact swE m 0 (by omega) _ _ _ _ (by decide) (by decide)
    | exact swE m 1 (by omega) _ _ _ _ (by decide) (by decide)

theorem run274r : check 4 T274r [a2] [b2]
    [.rw 0 2 true, .rw 1 1 true, .rw 2 0 false, .rw 1 3 false, .rw 0 4 false] = true := by
  decide +kernel

/-- (274) relabeled: the box on wire `2` (wire `1` idle) is the box on wire `1`
(wire `2` idle), controls `0, 3, 4` and the bulk. -/
theorem s274r (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [a2]) (wc 5 (m + 5) [b2]) :=
  check_sound (frame 4) ih (T274r_ok m ih) run274r

def T275 : SE.Tbl :=
  [([bx0], [wW, cC, wV, cC]), ([a2], [b2]), ([.s (.S 1), cC, .s (.S 1)], [a2])]

theorem T275_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T275 := by
  intro e he
  simp only [T275, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact t269 m
  · exact s274r m ih
  · have h := swE m 1 (by omega) .box [1] [(0, true), (3, true), (4, true)] true (by decide)
      (by decide)
    have e : swapG 1 .box [1] [(0, true), (3, true), (4, true)] true = a2 := by decide
    rw [e] at h
    exact h

theorem run275 : check 4 T275 [bx0, .s (.S 1)] [.s (.S 1), bx0]
    [.rw 0 0 false,
     .sem 3 0 [.s (.S 1), .s (.S 1)] 4, .rw 4 2 false, .rw 4 1 false,
     .sem 2 2 [.s (.S 1), wV] 4,
     .sem 1 0 [.s (.S 1), .s (.S 1)] 4, .rw 2 2 false, .rw 2 1 false,
     .sem 0 2 [.s (.S 1), wW] 4,
     .rw 1 0 true] = true := by
  decide +kernel

/-- (275) on five local wires: the box commutes with the swap of the
controls `1, 2`. -/
theorem s275 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0, .s (.S 1)]) (wc 5 (m + 5) [.s (.S 1), bx0]) :=
  check_sound (frame 4) ih (T275_ok m ih) run275

end QCert.RealCliffordCH.Sec8.D.N8
