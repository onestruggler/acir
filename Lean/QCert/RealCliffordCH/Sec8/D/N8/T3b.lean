/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three wires: the statements that are semantic steps

On three wires the box with two controls, the multi-controlled `H` with one
control and their coloured versions are gates on the wires `1, 2` (`CZ`,
`CH`, conjugated by `X` on wire `2`), so (299), (301), (302), (310), (312)
there are semantic steps (Lemma 5.1, wire `0` removed), and so are the cases
of Lemmas D.9 and D.11 at the canonical position.  On two wires those cases
are completeness there (`base0_box`, `base0_hg`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.T3

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

abbrev lK1 : Lt := .s (.K 1)
abbrev lZ2 : Lt := .s (.Z 2)
abbrev lH2 : Lt := .s (.H 2)

def Bx2w3 : Lt := .g .box [0] [(1, true), (2, false)] false
def D33 : Lt := .g .box [0] [(1, true)] false
def Bq3 : Lt := .g .box [1] [(2, true)] false
def hg3T : Lt := .g .hg [0, 1] [(2, true)] false
def hg3F : Lt := .g .hg [0, 1] [(2, false)] false
def hg3N : Lt := .g .hg [0, 1] [] false
def hg12_3 : Lt := .g .hg [1, 2] [] false

def T3b : SE.Tbl :=
  [([B3], [lC1]), ([Bx2w3], xL 2 ++ [lC1] ++ xL 2), ([D33], [lZ1]), ([hg3T], [lK1]),
   ([hg3F], xL 2 ++ [lK1] ++ xL 2), ([hg3N], [lH1])]

set_option maxRecDepth 100000 in
theorem T3b_ok : AllD 3 0 T3b := by
  intro e he
  simp only [T3b, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact der_of_eq (by rfl)

theorem run299_3 : check 2 T3b [B3, B3] [] [.rw 0 0 false, .rw 1 0 false, .sem 0 2 [] 0] = true := by
  decide +kernel

theorem t299 (ih : IH 3) : Derivable (theory 3) (wc 3 3 [B3, B3]) (wc 3 3 []) :=
  check_sound (frame 2) (m := 0) ih T3b_ok run299_3

theorem run301_3 : check 2 T3b [B3, Bx2w3] [D33]
    [.rw 0 0 false, .rw 1 1 false, .sem 0 8 [lZ1] 0, .rw 0 2 true] = true := by
  decide +kernel

theorem t301 (ih : IH 3) : Derivable (theory 3) (wc 3 3 [B3, Bx2w3]) (wc 3 3 [D33]) :=
  check_sound (frame 2) (m := 0) ih T3b_ok run301_3

theorem run302_3 : check 2 T3b [Bx2w3, B3] [D33]
    [.rw 0 1 false, .rw 7 0 false, .sem 0 8 [lZ1] 0, .rw 0 2 true] = true := by
  decide +kernel

theorem t302 (ih : IH 3) : Derivable (theory 3) (wc 3 3 [Bx2w3, B3]) (wc 3 3 [D33]) :=
  check_sound (frame 2) (m := 0) ih T3b_ok run302_3

theorem run310T_3 : check 2 T3b [hg3T, hg3F] [hg3N]
    [.rw 0 3 false, .rw 1 4 false, .sem 0 8 [lH1] 0, .rw 0 5 true] = true := by
  decide +kernel

theorem run310F_3 : check 2 T3b [hg3F, hg3T] [hg3N]
    [.rw 0 4 false, .rw 7 3 false, .sem 0 8 [lH1] 0, .rw 0 5 true] = true := by
  decide +kernel

theorem t310 (ih : IH 3) (b : Bool) :
    Derivable (theory 3) (wc 3 3 (if b then [hg3T, hg3F] else [hg3F, hg3T])) (wc 3 3 [hg3N]) := by
  cases b
  · exact check_sound (frame 2) (m := 0) ih T3b_ok run310F_3
  · exact check_sound (frame 2) (m := 0) ih T3b_ok run310T_3

theorem run312T_3 : check 2 T3b [hg3T, hg3T] [] [.rw 0 3 false, .rw 1 3 false, .sem 0 2 [] 0] = true := by
  decide +kernel

theorem run312F_3 : check 2 T3b [hg3F, hg3F] []
    [.rw 0 4 false, .rw 7 4 false, .sem 0 14 [] 0] = true := by
  decide +kernel

theorem t312 (ih : IH 3) (b : Bool) :
    Derivable (theory 3) (wc 3 3 (if b then [hg3T, hg3T] else [hg3F, hg3F])) (wc 3 3 []) := by
  cases b
  · exact check_sound (frame 2) (m := 0) ih T3b_ok run312F_3
  · exact check_sound (frame 2) (m := 0) ih T3b_ok run312T_3

/-! ## The cases of Lemmas D.9 and D.11 on three wires -/

theorem runB1_3 (x : L) (hx : x = .H 0 ∨ x = .Z 0) :
    check 2 T3b [.s x, B3] [B3, .s x] [.rw 1 0 false, .sw 0, .rw 0 0 true] = true := by
  rcases hx with rfl | rfl <;> decide +kernel

theorem runB2_3 (x : L) (hx : x = .C 0 ∨ x = .K 0) :
    check 2 T3b [.s x, Bq3] [Bq3, .s x] [.sem 1 1 [lZ2] 0, .sw 0, .sem 0 1 [Bq3] 0] = true := by
  rcases hx with rfl | rfl <;> decide +kernel

theorem runH1_3 (x : L) (hx : x = .H 0 ∨ x = .Z 0) :
    check 2 T3b [.s x, hg3T] [hg3T, .s x] [.rw 1 3 false, .sw 0, .rw 0 3 true] = true := by
  rcases hx with rfl | rfl <;> decide +kernel

theorem runH2_3 (x : L) (hx : x = .C 0 ∨ x = .K 0) :
    check 2 T3b [.s x, hg12_3] [hg12_3, .s x] [.sem 1 1 [lH2] 0, .sw 0, .sem 0 1 [hg12_3] 0] = true := by
  rcases hx with rfl | rfl <;> decide +kernel

/-! ## Two wires: completeness there -/

theorem base0_box (h2 : CompleteAt 2) (m : ℕ) (x : L) (hm : 1 ≤ m) (hm2 : m + 0 ≤ 2)
    (hx : x.lo + x.wd ≤ m) (hxS : ∀ j, x ≠ .S j) :
    Derivable (theory 2) (BoxM 2 m * x.circ 2) (x.circ 2 * BoxM 2 m) := by
  apply h2
  rcases (by omega : m = 1 ∨ m = 2) with rfl | rfl <;>
  cases x with
  | S j => exact absurd rfl (hxS j)
  | H j => simp only [L.lo, L.wd] at hx; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
      first | omega | exact Fast.sem_of_fast (by decide +kernel)
  | Z j => simp only [L.lo, L.wd] at hx; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
      first | omega | exact Fast.sem_of_fast (by decide +kernel)
  | C j => simp only [L.lo, L.wd] at hx; obtain rfl : j = 0 := by omega
           first | omega | exact Fast.sem_of_fast (by decide +kernel)
  | K j => simp only [L.lo, L.wd] at hx; obtain rfl : j = 0 := by omega
           first | omega | exact Fast.sem_of_fast (by decide +kernel)

theorem base0_hg (h2 : CompleteAt 2) (m : ℕ) (x : L) (hm : 1 ≤ m) (hm2 : m + 1 ≤ 2)
    (hx : x.lo + x.wd ≤ m) (hxS : ∀ j, x ≠ .S j) :
    Derivable (theory 2) (HgM 2 m * x.circ 2) (x.circ 2 * HgM 2 m) := by
  apply h2
  obtain rfl : m = 1 := by omega
  cases x with
  | S j => exact absurd rfl (hxS j)
  | H j => simp only [L.lo, L.wd] at hx; obtain rfl : j = 0 := by omega
           exact Fast.sem_of_fast (by decide +kernel)
  | Z j => simp only [L.lo, L.wd] at hx; obtain rfl : j = 0 := by omega
           exact Fast.sem_of_fast (by decide +kernel)
  | C j => simp only [L.lo, L.wd] at hx; omega
  | K j => simp only [L.lo, L.wd] at hx; omega

end QCert.RealCliffordCH.Sec8.D.N8
