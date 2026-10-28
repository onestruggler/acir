/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The frame steps, case by case

The equations `T_c · Φ(y) ≈ τ(c, y)₁ · T_{τ(c, y)₂}` (`FrameSteps.lean`) on
natural-number indices, one lemma per case of the coset action `τ` of
Definition A.2 (`tauZHn`, `w2n`, `tXn`, `w3n`, `w7n` are the words of `τ` on
natural-number indices).  The Hadamard-free comparisons are Corollary A.5,
decided at the numerals `0, 1, 2, …` and renamed (`A5v`); the sink `g` may be
`0` when the generator avoids `0`, so those comparisons split on `g = 0`.
-/
import QCert.RealCliffordCH.Sec8.A.FrameSteps

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

variable (n) in
/-- `τ(H[0,1], (-1)[a])`. -/
def tauZHn (a : ℕ) : List (PG (2 ^ n)) :=
  if a = 0 ∨ a = 1 then [Zz n 1 a] else [Zx n a 0 1]

variable (n) in
/-- `τ(ε, X_[a,b])`. -/
def w2n (a b : ℕ) : List (PG (2 ^ n)) :=
  if a = 1 ∨ b = 1 then [Zx n (if a = 1 then b else a) a b] else [Zx n 1 a b]

variable (n) in
/-- `τ(H[0,1], X_[a,b])` (`isH`) and `τ(H[0,1](-1)[1], X_[a,b])`. -/
def tXn (isH : Bool) (a b : ℕ) : List (PG (2 ^ n)) :=
  if a = 0 ∧ b = 1 then [Zx n (if isH then 1 else 0) 0 1]
  else if a = 0 then [Xx n 0 1 a b, Hh n (if a = 0 then b else a) 1 0 1]
  else if a = 1 then (if isH then [Zx n (if a = 1 then b else a) a b] else [Xx n 0 1 a b]) ++
    [Hh n 0 (if a = 1 then b else a) 0 1]
  else [Xx n a b 0 1]

variable (n) in
/-- `τ((-1)[1], H_[a,b])`. -/
def w3n (a b : ℕ) : List (PG (2 ^ n)) :=
  if a = 1 ∨ b = 1 then [Zx n b a b, Hh n a b 0 1] else [Hh n a b 0 1]

variable (n) in
/-- `τ(H[0,1](-1)[1], H_[a,b])`. -/
def w7n (a b : ℕ) : List (PG (2 ^ n)) :=
  if a = 1 ∨ b = 1 then [Hh n 0 1 a b, Zx n a a b] else [Hh n 0 1 a b]

/-- Corollary A.5 at the distinct indices `l`, decided at the numerals: the
two words are given at the numerals and renamed. -/
macro "a5at " nn:term:max l:term:max m:term:max L:term:max L₂:term:max : tactic =>
  `(tactic| (
    have t := A5v (n := $nn) (m := $m) (by omega) $l rfl (by simp <;> omega) (by bdl) $L $L₂
      (by decide)
    simp only [rv, NL.ren, NL.toPG, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero] at t
    exact t))

/-! ## The Hadamard-free comparisons -/

section Tails

variable (h8 : 8 ≤ 2 ^ n)
include h8

theorem tl_Ze {a g : ℕ} (ha : a < 2 ^ n) (hg : g < 2 ^ n) (hg1 : g ≠ 1) (hag : a ≠ g) :
    D8 n [Zz n a g] [Zz n 1 a, Zz n 1 g] := by
  rcases eq_or_ne a 1 with rfl | ha1
  · a5at n [1, g] 2 [NL.zz 0 1] [NL.zz 0 0, NL.zz 0 1]
  · a5at n [1, a, g] 3 [NL.zz 1 2] [NL.zz 0 1, NL.zz 0 2]

theorem tl_Zz {a g : ℕ} (ha : a < 2 ^ n) (hg : g < 2 ^ n) (hg1 : g ≠ 1) (hag : a ≠ g) :
    D8 n [Zz n 1 g, Zz n a g] [Zz n 1 a] := by
  rcases eq_or_ne a 1 with rfl | ha1
  · a5at n [1, g] 2 [NL.zz 0 1, NL.zz 0 1] [NL.zz 0 0]
  · a5at n [1, a, g] 3 [NL.zz 0 2, NL.zz 1 2] [NL.zz 0 1]

theorem tl_Zh0 {g : ℕ} (hg : g < 2 ^ n) (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    D8 n [Zz n 1 0, Zz n 1 g] [Zz n 0 g] := by
  a5at n [0, 1, g] 3 [NL.zz 1 0, NL.zz 1 2] [NL.zz 0 2]

theorem tl_Z11 : D8 n [Zz n 1 1] [] := by a5at n [1] 1 [NL.zz 0 0] []

theorem tl_Zh {a g : ℕ} (ha : a < 2 ^ n) (hg : g < 2 ^ n) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hg1 : g ≠ 1) (hag : a ≠ g) :
    D8 n [Zx n 1 0 1, Zx n a 0 1, Zz n 1 g] [Zz n a g] := by
  rcases eq_or_ne g 0 with rfl | hg0
  · a5at n [0, 1, a] 3 [NL.zx 1 0 1, NL.zx 2 0 1, NL.zz 1 0] [NL.zz 2 0]
  · a5at n [0, 1, a, g] 4 [NL.zx 1 0 1, NL.zx 2 0 1, NL.zz 1 3] [NL.zz 2 3]

theorem tl_Zhz0 {g : ℕ} (hg : g < 2 ^ n) (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    D8 n [Zz n 1 g, Zz n 0 g] [Zz n 1 0] := by
  a5at n [0, 1, g] 3 [NL.zz 1 2, NL.zz 0 2] [NL.zz 1 0]

theorem tl_Zhz1 {g : ℕ} (hg : g < 2 ^ n) (hg1 : g ≠ 1) :
    D8 n [Zz n 1 g, Zz n 1 g] [Zz n 1 1] := by
  a5at n [1, g] 2 [NL.zz 0 1, NL.zz 0 1] [NL.zz 0 0]

theorem tl_Zhz {a g : ℕ} (ha : a < 2 ^ n) (hg : g < 2 ^ n) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hg1 : g ≠ 1) (hag : a ≠ g) :
    D8 n [Zz n 1 g, Zz n a g] [Zx n 1 0 1, Zx n a 0 1] := by
  rcases eq_or_ne g 0 with rfl | hg0
  · a5at n [0, 1, a] 3 [NL.zz 1 0, NL.zz 2 0] [NL.zx 1 0 1, NL.zx 2 0 1]
  · a5at n [0, 1, a, g] 4 [NL.zz 1 3, NL.zz 2 3] [NL.zx 1 0 1, NL.zx 2 0 1]

theorem tl_Xe01 {g : ℕ} (hg : g < 2 ^ n) (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    D8 n [Zx n g 0 1] [Zx n 0 0 1, Zz n 1 g] := by
  a5at n [0, 1, g] 3 [NL.zx 2 0 1] [NL.zx 0 0 1, NL.zz 1 2]

theorem tl_Xe1b {b g : ℕ} (hb : b < 2 ^ n) (hg : g < 2 ^ n) (hb1 : b ≠ 1) (hg1 : g ≠ 1)
    (hbg : b ≠ g) : D8 n [Zx n g 1 b] [Zx n b 1 b, Zz n 1 g] := by
  a5at n [1, b, g] 3 [NL.zx 2 0 1] [NL.zx 1 0 1, NL.zz 0 2]

theorem tl_Xeab {a b g : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hg : g < 2 ^ n) (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hg1 : g ≠ 1) (hag : a ≠ g) (hbg : b ≠ g) :
    D8 n [Zx n g a b] [Zx n 1 a b, Zz n 1 g] := by
  a5at n [1, a, b, g] 4 [NL.zx 3 1 2] [NL.zx 0 1 2, NL.zz 0 3]

theorem tl_Xz {a b g : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) (hg1 : g ≠ 1)
    (hag : a ≠ g) (hbg : b ≠ g) (hg : g < 2 ^ n) :
    D8 n [Zz n 1 g, Zx n g a b] [Zx n 1 a b] := by
  rcases eq_or_ne a 1 with rfl | ha1
  · a5at n [1, b, g] 3 [NL.zz 0 2, NL.zx 2 0 1] [NL.zx 0 0 1]
  rcases eq_or_ne b 1 with rfl | hb1
  · a5at n [a, 1, g] 3 [NL.zz 1 2, NL.zx 2 0 1] [NL.zx 1 0 1]
  · a5at n [1, a, b, g] 4 [NL.zz 0 3, NL.zx 3 1 2] [NL.zx 0 1 2]

theorem tl_Xh01 {g : ℕ} (hg : g < 2 ^ n) (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    D8 n [Zx n 1 0 1, Zx n 1 0 1, Zx n 1 0 1, Zz n 1 g] [Zx n g 0 1] := by
  a5at n [0, 1, g] 3 [NL.zx 1 0 1, NL.zx 1 0 1, NL.zx 1 0 1, NL.zz 1 2] [NL.zx 2 0 1]

theorem tl_Xh0b {b g : ℕ} (hb : b < 2 ^ n) (hg : g < 2 ^ n) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hg0 : g ≠ 0) (hg1 : g ≠ 1) (hbg : b ≠ g) :
    D8 n [Zx n 1 0 1, Xx n 0 1 0 b, Zz n 1 g] [Zx n g 0 b] := by
  a5at n [0, 1, b, g] 4 [NL.zx 1 0 1, NL.xx 0 1 0 2, NL.zz 1 3] [NL.zx 3 0 2]

theorem tl_Xh1b {b g : ℕ} (hb : b < 2 ^ n) (hg : g < 2 ^ n) (hb1 : b ≠ 1) (hg1 : g ≠ 1)
    (hbg : b ≠ g) : D8 n [Zx n b 1 b, Zz n 1 g] [Zx n g 1 b] := by
  a5at n [1, b, g] 3 [NL.zx 1 0 1, NL.zz 0 2] [NL.zx 2 0 1]

theorem tl_Xhab {a b g : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hg : g < 2 ^ n) (hab : a ≠ b)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hg1 : g ≠ 1) (hag : a ≠ g)
    (hbg : b ≠ g) : D8 n [Zx n 1 0 1, Xx n a b 0 1, Zz n 1 g] [Zx n g a b] := by
  rcases eq_or_ne g 0 with rfl | hg0
  · a5at n [0, 1, a, b] 4 [NL.zx 1 0 1, NL.xx 2 3 0 1, NL.zz 1 0] [NL.zx 0 2 3]
  · a5at n [0, 1, a, b, g] 5 [NL.zx 1 0 1, NL.xx 2 3 0 1, NL.zz 1 4] [NL.zx 4 2 3]

theorem tl_Xhz01 {g : ℕ} (hg : g < 2 ^ n) (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    D8 n [Zx n 1 0 1, Zx n 1 0 1, Zx n 0 0 1] [Zz n 1 g, Zx n g 0 1] := by
  a5at n [0, 1, g] 3 [NL.zx 1 0 1, NL.zx 1 0 1, NL.zx 0 0 1] [NL.zz 1 2, NL.zx 2 0 1]

theorem tl_Xhz0b {b g : ℕ} (hb : b < 2 ^ n) (hg : g < 2 ^ n) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hg0 : g ≠ 0) (hg1 : g ≠ 1) (hbg : b ≠ g) :
    D8 n [Zx n 1 0 1, Xx n 0 1 0 b] [Zz n 1 g, Zx n g 0 b] := by
  a5at n [0, 1, b, g] 4 [NL.zx 1 0 1, NL.xx 0 1 0 2] [NL.zz 1 3, NL.zx 3 0 2]

theorem tl_Xhz1b {b g : ℕ} (hb : b < 2 ^ n) (hg : g < 2 ^ n) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hg1 : g ≠ 1) (hbg : b ≠ g) :
    D8 n [Zx n 1 0 1, Xx n 0 1 1 b] [Zz n 1 g, Zx n g 1 b] := by
  rcases eq_or_ne g 0 with rfl | hg0
  · a5at n [0, 1, b] 3 [NL.zx 1 0 1, NL.xx 0 1 1 2] [NL.zz 1 0, NL.zx 0 1 2]
  · a5at n [0, 1, b, g] 4 [NL.zx 1 0 1, NL.xx 0 1 1 2] [NL.zz 1 3, NL.zx 3 1 2]

theorem tl_Xhzab {a b g : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hg : g < 2 ^ n) (hab : a ≠ b)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hg1 : g ≠ 1) (hag : a ≠ g)
    (hbg : b ≠ g) : D8 n [Zx n 1 0 1, Xx n a b 0 1] [Zz n 1 g, Zx n g a b] := by
  rcases eq_or_ne g 0 with rfl | hg0
  · a5at n [0, 1, a, b] 4 [NL.zx 1 0 1, NL.xx 2 3 0 1] [NL.zz 1 0, NL.zx 0 2 3]
  · a5at n [0, 1, a, b, g] 5 [NL.zx 1 0 1, NL.xx 2 3 0 1] [NL.zz 1 4, NL.zx 4 2 3]

theorem tl_Hz {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) :
    D8 n [Zx n a b a] [Zx n b a b, Zx n b a b, Zx n b a b] := by
  a5at n [a, b] 2 [NL.zx 0 1 0] [NL.zx 1 0 1, NL.zx 1 0 1, NL.zx 1 0 1]

theorem tl_Hhz {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) :
    D8 n [Zx n a b a] [Zx n a a b] := by
  a5at n [a, b] 2 [NL.zx 0 1 0] [NL.zx 0 0 1]

end Tails

end QCert.RealCliffordCH.Sec8
