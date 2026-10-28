/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (a): one step of the coset action on `X` and `H`

The coset action `τ` (`tauA`) followed through `σ(H_[a,b]H_[c,d])` meets the
generators `X_[x,y]`, `H_[x,y]` (`x < y`) at every coset.  Each step is a
relation `T_c · Φ(g) ≈ τ(c, g)₁ · T_{τ(c, g)₂}` between words over `𝒫_N`, where

* `Φ(H_[x,y]) = H_[x,y]H_[p,q]` and `Φ(X_[x,y]) = (-1)_[s]X_[x,y]`, for a pair
  `p, q` and a sink `s` away from `0, 1, x, y`;
* `T_ε = ε`, `T_{(-1)[1]} = (-1)_[1](-1)_[s]`, `T_{H[0,1]} = H_[0,1]H_[p,q]`,
  `T_{H[0,1](-1)[1]} = H_[0,1]H_[p,q] · (-1)_[1](-1)_[s]`.

The words of `τ` are written here on natural-number indices (`w2`, `w3`,
`tX`, `w7`); `stepS1` … `stepS8` are the eight steps, each from Equation (65)
through (66), (71), the moves `cjA`, `cjT`, the reversal `flip1` and
Corollary A.5.  Every step was checked numerically first.
-/
import QCert.RealCliffordCH.Sec8.A.ItemATools

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- A generator on `x < y`, a pair `p, q` and a sink `g` away from `0, 1, x, y`. -/
structure StepSet (n x y p q g : ℕ) : Prop where
  xy : x < y
  y2 : y < 2 ^ n
  p2 : p < 2 ^ n
  q2 : q < 2 ^ n
  g2 : g < 2 ^ n
  pq : p ≠ q
  p0 : p ≠ 0
  p1 : p ≠ 1
  px : p ≠ x
  py : p ≠ y
  q0 : q ≠ 0
  q1 : q ≠ 1
  qx : q ≠ x
  qy : q ≠ y
  g0 : g ≠ 0
  g1 : g ≠ 1
  gx : g ≠ x
  gy : g ≠ y
  gp : g ≠ p
  gq : g ≠ q

variable (n) in
/-- `τ(ε, X_[x,y])` -/
def w2 (x y : ℕ) : List (PG (2 ^ n)) :=
  if x = 1 ∨ y = 1 then [Zx n (if x = 1 then y else x) x y] else [Zx n 1 x y]

variable (n) in
/-- `τ((-1)[1], H_[x,y])` -/
def w3 (x y : ℕ) : List (PG (2 ^ n)) :=
  if x = 1 ∨ y = 1 then [Zx n y x y, Hh n x y 0 1] else [Hh n x y 0 1]

variable (n) in
/-- `τ(H[0,1], X_[x,y])` (`isH`) and `τ(H[0,1](-1)[1], X_[x,y])`. -/
def tX (isH : Bool) (x y : ℕ) : List (PG (2 ^ n)) :=
  if x = 0 ∧ y = 1 then [Zx n (if isH then 1 else 0) 0 1]
  else if x = 0 then [Xx n 0 1 x y, Hh n y 1 0 1]
  else if x = 1 then (if isH then [Zx n y x y] else [Xx n 0 1 x y]) ++ [Hh n 0 y 0 1]
  else [Xx n x y 0 1]

variable (n) in
/-- `τ(H[0,1](-1)[1], H_[x,y])` -/
def w7 (x y : ℕ) : List (PG (2 ^ n)) :=
  if x = 1 ∨ y = 1 then [Hh n 0 1 x y, Zx n x x y] else [Hh n 0 1 x y]

/-- Values of a letter's permutation and signs. -/
macro "pm_tac" : tactic => `(tactic| (simp only [NL.perm, swN, id]; split_ifs <;> omega))

macro "sg_tac" : tactic => `(tactic| (simp only [negL, permL, NL.neg, NL.perm, swN, id]; split_ifs <;> first | rfl | omega | (exfalso; omega)))

/-- Bounds of a list of letters. -/
macro "bd2" : tactic => `(tactic| (simp only [List.forall_mem_cons, NL.Bd, List.mem_nil_iff, false_implies, implies_true, and_true] <;> omega))

/-- Proper letters. -/
macro "pr2" : tactic => `(tactic| (simp only [List.forall_mem_cons, NL.Pr, List.mem_nil_iff, false_implies, implies_true, and_true, true_and, ne_eq] <;> omega))

section Steps

variable (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {x y p q g : ℕ} (st : StepSet n x y p q g)
include h8 hE st

theorem stepS1 : D8 n [Hh n x y p q] [Hh n x y 0 1, Hh n 0 1 p q] := by
  obtain ⟨xy, y2, p2, q2, g2, pq, -⟩ := st
  exact (e71 h8 hE (by omega) y2 (by omega) (by omega) p2 q2 (by omega) (by norm_num) pq).symm

theorem stepS2 : D8 n [Zx n g x y] (w2 n x y ++ [Zz n 1 g]) := by
  obtain ⟨xy, y2, p2, q2, g2, pq, p0, p1, px, py, q0, q1, qx, qy, g0, g1, gx, gy, gp, gq⟩ := st
  have hN : 4 ≤ 2 ^ n := by omega
  unfold w2
  by_cases h1 : x = 1
  · subst h1
    rw [if_pos (Or.inl rfl), if_pos rfl]
    exact a5NL (L := [NL.zx g 1 y]) (L' := [NL.zx y 1 y, NL.zz 1 g]) hN (by bd2) (by bd2)
      (by pr2) (by pr2) (fun j hj => by nl_eval)
  by_cases h2 : y = 1
  · subst h2
    rw [if_pos (Or.inr rfl), if_neg h1]
    exact a5NL (L := [NL.zx g x 1]) (L' := [NL.zx x x 1, NL.zz 1 g]) hN (by bd2) (by bd2)
      (by pr2) (by pr2) (fun j hj => by nl_eval)
  rw [if_neg (by omega)]
  exact a5NL (L := [NL.zx g x y]) (L' := [NL.zx 1 x y, NL.zz 1 g]) hN (by bd2) (by bd2)
    (by pr2) (by pr2) (fun j hj => by nl_eval)

theorem stepS8 : D8 n [Zz n 1 g, Zx n g x y] [Zx n 1 x y] := by
  obtain ⟨xy, y2, p2, q2, g2, pq, p0, p1, px, py, q0, q1, qx, qy, g0, g1, gx, gy, gp, gq⟩ := st
  exact a5NL (L := [NL.zz 1 g, NL.zx g x y]) (L' := [NL.zx 1 x y]) (by omega) (by bd2)
    (by bd2) (by pr2) (by pr2) (fun j hj => by nl_eval)

theorem stepS5 : D8 n [Hh n 0 1 p q, Hh n x y p q] [Hh n 0 1 x y] := by
  obtain ⟨xy, y2, p2, q2, g2, pq, p0, p1, px, py, q0, q1, qx, qy, -⟩ := st
  have hD : Distinct4 x y p q := ⟨by omega, by omega, by omega, by omega, by omega, pq⟩
  refine (D8.seg [Hh n 0 1 p q] [] (e66 h8 hE (by omega) y2 p2 q2 hD) (by simp) rfl).trans ?_
  exact e71 h8 hE (by omega) (by omega) p2 q2 (by omega) y2 (by norm_num) pq (by omega)

end Steps

end QCert.RealCliffordCH.Sec8
