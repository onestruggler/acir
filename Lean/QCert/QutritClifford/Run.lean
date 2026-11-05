/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The decision procedures of the rewriting engine

Toward Theorem 4.4.  The computational part of the engine
(`Engine.lean`, `Local.lean`), with no Mathlib import, so that the modules
deciding stored libraries (`Lib2Chk*`, ...) load nothing else:

* letters (`Lt`), their wires, and equality up to commuting letters
  (`sameTr`);
* words stored as numbers: in base 9 for the certificates (`decW`), in
  base 16 for the libraries (`dec16`);
* Pauli tableaux on one and two wires (`run1`, `run2`) and the free steps
  on two and three wires (`fo2`, `fo3`);
* the base tables (`base2`, `base3`) and inverse words (`invW`);
* the check of a stored library, lemma by lemma, on codes (`stepX`,
  `runX`, `libLemOk`).

Their meaning is in `Engine.lean` and `Local.lean`.
-/

namespace QCert.QutritClifford

local notation "ℕ" => Nat

/-- Letters of derivations: `H` and `S` on wire `j`, `CZ` on wires `j, j + 1`. -/
inductive Lt
  | H (j : ℕ)
  | S (j : ℕ)
  | C (j : ℕ)
  deriving DecidableEq, Repr

namespace Lt

/-- The lowest wire of a letter. -/
def lo : Lt → ℕ
  | H j => j
  | S j => j
  | C j => j

/-- The highest wire of a letter. -/
def hi : Lt → ℕ
  | H j => j
  | S j => j
  | C j => j + 1

/-- The letter one wire down. -/
def down : Lt → Lt
  | H j => H (j - 1)
  | S j => S (j - 1)
  | C j => C (j - 1)

/-- Letters on disjoint wires. -/
def disj (x y : Lt) : Bool := x.hi < y.lo || y.hi < x.lo

end Lt

/-- Boolean equality of letters, by `Nat.beq` on the wires. -/
def Lt.beq : Lt → Lt → Bool
  | .H i, .H j => i.beq j
  | .S i, .S j => i.beq j
  | .C i, .C j => i.beq j
  | _, _ => false

/-- `w` with the letter `t` taken out of the first place it occurs,
provided every letter before it is on wires disjoint from it. -/
def extract (t : Lt) : List Lt → Option (List Lt)
  | [] => none
  | y :: w => bif Lt.beq t y then some w
    else bif Lt.disj y t then (extract t w).map (y :: ·) else none

/-- `w` and `v` are the same word up to commuting adjacent letters on
disjoint wires: the letters of `v` are taken out of `w` in order, each from
the first place it occurs (`extract`).  This is one pass over the words,
with a few comparisons per letter; it replaced a comparison of canonical
forms, and with it the explicit swaps of adjacent letters the derivations
used to carry before each step (see the README, "Typechecking cost"). -/
def sameTr : List Lt → List Lt → Bool
  | [], [] => true
  | _ :: _, [] => false
  | w, t :: ts => match extract t w with
    | some w' => sameTr w' ts
    | none => false

abbrev Tbl := List (List Lt × List Lt)

/-! ### Words as numbers -/

/-- The letter of a digit: `1`-`8` are `H₀ S₀ H₁ S₁ H₂ S₂ C₀ C₁`. -/
def digL : ℕ → Lt
  | 1 => .H 0
  | 2 => .S 0
  | 3 => .H 1
  | 4 => .S 1
  | 5 => .H 2
  | 6 => .S 2
  | 7 => .C 0
  | _ => .C 1

def decWF : ℕ → ℕ → List Lt
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else digL (n % 9) :: decWF f (n / 9)

/-- The word of a number. -/
def decW (n : ℕ) : List Lt := decWF 250 n

/-- Pauli data on one wire: `ω^c X^a Z^b`. -/
structure P1 where
  c : Fin 3
  a : Fin 3
  b : Fin 3
  deriving DecidableEq

/-- Pauli data on two wires. -/
structure P2 where
  c : Fin 3
  a0 : Fin 3
  b0 : Fin 3
  a1 : Fin 3
  b1 : Fin 3
  deriving DecidableEq

def t1 : Lt → P1 → P1
  | .H 0, p => ⟨p.c + 2 * p.a * p.b, 2 * p.b, p.a⟩
  | .S 0, p => ⟨p.c + p.a * (p.a - 1), p.a, p.b + 2 * p.a⟩
  | _, p => p

def t2 : Lt → P2 → P2
  | .H 0, p => ⟨p.c + 2 * p.a0 * p.b0, 2 * p.b0, p.a0, p.a1, p.b1⟩
  | .S 0, p => ⟨p.c + p.a0 * (p.a0 - 1), p.a0, p.b0 + 2 * p.a0, p.a1, p.b1⟩
  | .H 1, p => ⟨p.c + 2 * p.a1 * p.b1, p.a0, p.b0, 2 * p.b1, p.a1⟩
  | .S 1, p => ⟨p.c + p.a1 * (p.a1 - 1), p.a0, p.b0, p.a1, p.b1 + 2 * p.a1⟩
  | .C 0, p => ⟨p.c + p.a0 * p.a1, p.a0, p.b0 + p.a1, p.a1, p.b1 + p.a0⟩
  | _, p => p

def run1 : List Lt → P1 → P1
  | [], p => p
  | x :: l, p => run1 l (t1 x p)

def run2 : List Lt → P2 → P2
  | [], p => p
  | x :: l, p => run2 l (t2 x p)

/-- Letters on one wire, and on two wires. -/
def in1 (x : Lt) : Bool := x.hi == 0
def in2 (x : Lt) : Bool := x.hi ≤ 1

/-- Words on one wire acting alike on `X` and `Z`. -/
def same1 (s t : List Lt) : Bool :=
  run1 s ⟨0, 1, 0⟩ == run1 t ⟨0, 1, 0⟩ && run1 s ⟨0, 0, 1⟩ == run1 t ⟨0, 0, 1⟩

/-- Words on two wires acting alike on `X₀`, `Z₀`, `X₁`, `Z₁`. -/
def same2 (s t : List Lt) : Bool :=
  run2 s ⟨0, 1, 0, 0, 0⟩ == run2 t ⟨0, 1, 0, 0, 0⟩ &&
  run2 s ⟨0, 0, 1, 0, 0⟩ == run2 t ⟨0, 0, 1, 0, 0⟩ &&
  run2 s ⟨0, 0, 0, 1, 0⟩ == run2 t ⟨0, 0, 0, 1, 0⟩ &&
  run2 s ⟨0, 0, 0, 0, 1⟩ == run2 t ⟨0, 0, 0, 0, 1⟩

/-- On two wires: the letters on wire 0 and on wire 1. -/
def lo2 (x : Lt) : Bool := x.hi == 0
def hi2 (x : Lt) : Bool := x.lo == 1 && x.hi == 1
def hi1 (x : Lt) : Bool := 1 ≤ x.lo

/-- On three wires: the letters on wires 0, 1 and on wires 1, 2. -/
def lo3 (x : Lt) : Bool := x.hi ≤ 1
def hi3 (x : Lt) : Bool := 1 ≤ x.lo && x.hi ≤ 2

def fo2 (s t : List Lt) : Bool :=
  (s.all lo2 && t.all lo2 && same1 s t) ||
  (s.all hi2 && t.all hi2 && same1 (s.map Lt.down) (t.map Lt.down))

def fo3 (s t : List Lt) : Bool :=
  (s.all lo3 && t.all lo3 && same2 s t) ||
  (s.all hi3 && t.all hi3 && same2 (s.map Lt.down) (t.map Lt.down))

def W0 : List Lt := [.H 0, .H 1, .C 0, .H 0, .H 1, .C 0, .H 0, .H 1, .C 0]
def W1 : List Lt := [.H 1, .H 2, .C 1, .H 1, .H 2, .C 1, .H 1, .H 2, .C 1]
def XCw : List Lt := [.H 1, .C 0, .H 1, .H 1, .H 1]
def Spw : List Lt := [.H 0, .H 0, .S 0, .H 0, .H 0]

/-- (C6)-(C14), scalars dropped. -/
def base2 : Tbl :=
  [([.C 0, .C 0, .C 0], []),
   (W0 ++ W0, []),
   ([.S 1, .C 0], [.C 0, .S 1]),
   ([.H 1, .H 1, .C 0, .C 0], [.C 0, .H 1, .H 1]),
   ([.S 1] ++ W0, W0 ++ [.S 0]),
   ([.H 1] ++ W0, W0 ++ [.H 0]),
   ([.C 0] ++ W0, W0 ++ [.C 0]),
   ([.S 1] ++ XCw, XCw ++ [.C 0, .S 1] ++ Spw),
   ([.C 0] ++ XCw, XCw ++ [.C 0] ++ Spw ++ [.S 0])]

/-- (C15)-(C18). -/
def base3 : Tbl :=
  [([.C 0, .C 1], [.C 1, .C 0]),
   (W1 ++ W0 ++ W1, W0 ++ W1 ++ W0),
   ([.C 0] ++ W1 ++ W0, W1 ++ W0 ++ [.C 1]),
   ([.H 1, .C 1, .H 1, .H 1, .H 1, .C 0], [.C 0, .H 1, .C 1, .H 1, .H 1, .H 1] ++ W0 ++ [.C 1] ++ W0)]

/-- The inverse of a letter, a power of it. -/
def invL : Lt → List Lt
  | .H j => [.H j, .H j, .H j]
  | .S j => [.S j, .S j]
  | .C j => [.C j, .C j]

/-- The inverse of a word. -/
def invW : List Lt → List Lt
  | [] => []
  | x :: l => invW l ++ invL x

/-! ### The stored libraries: words as base-16 codes

A library lemma is checked on codes: a word is a number in base `16`, its
first letter the least significant digit (`dec16`; digits other than
`1`-`8` stand for no letter), so that a rewrite is arithmetic, which the
kernel does with GMP (`cat3`), where decoding the words into lists and
comparing them cost it a few hundred reductions per letter.  The words of
a step are stored with their lengths; the comparison of the word before a
step with the side of the equation (`sameH`) is equality of the codes, or,
when the two differ by commuting letters, equality below digit `p` and
from digit `p + w` on and `sameTr` on the window of `w` digits between,
`p` and `w` being stored with the step. -/

/-- The letter of a base-16 digit: `1`-`8` are `H₀ S₀ H₁ S₁ H₂ S₂ C₀ C₁`,
the other digits stand for no letter. -/
def dig16 (d : ℕ) : List Lt :=
  bif d.beq 1 then [.H 0] else bif d.beq 2 then [.S 0] else bif d.beq 3 then [.H 1] else
  bif d.beq 4 then [.S 1] else bif d.beq 5 then [.H 2] else bif d.beq 6 then [.S 2] else
  bif d.beq 7 then [.C 0] else bif d.beq 8 then [.C 1] else []

/-- Decoding with fuel, by primitive recursion (for the kernel). -/
noncomputable def dec16F (f : ℕ) : ℕ → List Lt :=
  Nat.rec (motive := fun _ => ℕ → List Lt) (fun _ => [])
    (fun _ ih n => bif n.beq 0 then [] else dig16 (n % 16) ++ ih (n / 16)) f

/-- The word of a base-16 code. -/
noncomputable def dec16 (n : ℕ) : List Lt := dec16F n n

/-- The digit of a letter (`0` for a letter on wires above `2`). -/
def code16 : Lt → ℕ
  | .H 0 => 1
  | .S 0 => 2
  | .H 1 => 3
  | .S 1 => 4
  | .H 2 => 5
  | .S 2 => 6
  | .C 0 => 7
  | .C 1 => 8
  | _ => 0

/-- The base-16 code of a word. -/
def enc16 : List Lt → ℕ
  | [] => 0
  | x :: w => code16 x + 16 * enc16 w

/-- `u ++ a ++ v` on codes, `u` of `lu` digits and `a` of `la`. -/
def cat3 (u lu a la v : ℕ) : ℕ := u + 16 ^ lu * (a + 16 ^ la * v)

/-- The words of two codes are equal up to commuting letters: the codes
are equal, or agree below digit `p` and from digit `p + w` on, with windows
of `w` digits that `sameTr` identifies. -/
noncomputable def sameH (c d p w : ℕ) : Bool :=
  c.beq d ||
    ((c % 16 ^ p).beq (d % 16 ^ p) && (c / 16 ^ (p + w)).beq (d / 16 ^ (p + w)) &&
      sameTr (dec16 (c / 16 ^ p % 16 ^ w)) (dec16 (d / 16 ^ p % 16 ^ w)))

/-- Entry `i` of a list, by primitive recursion (for the kernel). -/
noncomputable def nthX {α : Type} (l : List α) : ℕ → Option α :=
  List.rec (motive := fun _ => ℕ → Option α) (fun _ => none)
    (fun a _ ih i => Nat.rec (motive := fun _ => Option α) (some a) (fun i' _ => ih i') i) l

/-- A stored step: `(0, i, rev, u, |u|, v, p, w, 0, 0)` rewrites with
entry `i` of the table (right to left when `rev = 1`) at `u`, `v`;
`(1, u, |u|, s, |s|, t, |t|, v, p, w)` replaces `s` by `t` at `u`, `v`, a
free step; `p`, `w` are the hints of `sameH`. -/
abbrev SX := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- A stored lemma `(l, |l|, r, |r|, p, w, steps)`: `l = r`, by the steps,
with the hints of the comparison at the end. -/
abbrev LX := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List SX

/-- Entry `j < n` of the table `B` followed by the lemmas of `D`, as codes
with their lengths. -/
noncomputable def tbX (B : Tbl) (D : List LX) (n j : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  bif Nat.blt j n then
    bif Nat.blt j B.length then (nthX B j).map fun e => (enc16 e.1, e.1.length, enc16 e.2, e.2.length)
    else (nthX D (j - B.length)).map fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1)
  else none

/-- Replace `x` (of `lx` digits) by `y` (of `ly`) between `u` (of `lu`) and
`v`, the word before being `cur` (with the hints `p`, `w`). -/
def ruleX (sm : ℕ → ℕ → ℕ → ℕ → Bool) (cur u lu v p w x lx y ly : ℕ) : Option ℕ :=
  bif Nat.blt u (16 ^ lu) && Nat.blt x (16 ^ lx) && Nat.blt y (16 ^ ly) &&
      sm cur (cat3 u lu x lx v) p w then
    some (cat3 u lu y ly v)
  else none

section RunX

variable (fo : List Lt → List Lt → Bool) (T : ℕ → Option (ℕ × ℕ × ℕ × ℕ))

/-- One stored step. -/
noncomputable def stepX (cur : ℕ) : SX → Option ℕ
  | (k, a1, a2, a3, a4, a5, a6, a7, a8, a9) =>
    bif k.beq 0 then
      match T a1 with
      | none => none
      | some (l, ll, r, lr) =>
        bif a2.beq 1 then ruleX sameH cur a3 a4 a5 a6 a7 r lr l ll
        else ruleX sameH cur a3 a4 a5 a6 a7 l ll r lr
    else bif k.beq 1 then
      bif fo (dec16 a3) (dec16 a5) then ruleX sameH cur a1 a2 a7 a8 a9 a3 a4 a5 a6 else none
    else none

/-- A run of stored steps. -/
noncomputable def runX : List SX → ℕ → Option ℕ
  | [], c => some c
  | st :: sts, c => match stepX fo T c st with
    | some c' => runX sts c'
    | none => none

end RunX

/-- Lemma `i` of a stored library checks over the table before it. -/
noncomputable def libLemOk (fo : List Lt → List Lt → Bool) (B : Tbl) (D : List LX) (i : ℕ) : Bool :=
  match nthX D i with
  | none => false
  | some (l, _, r, _, p, w, sts) =>
    match runX fo (tbX B D (B.length + i)) sts l with
    | none => false
    | some c => sameH c r p w

/-- The table of a library: `B`, then the lemmas of `D`. -/
noncomputable def libTbl (B : Tbl) (D : List LX) : Tbl :=
  B ++ D.map fun e => (dec16 e.1, dec16 e.2.2.1)

/-- Every index below `j + 1` passes, from every index below `j` and `j`. -/
theorem upto_succ {P : Nat → Bool} {j : Nat} (h : ∀ i < j, P i = true) (hj : P j = true) :
    ∀ i < j + 1, P i = true := by
  intro i hi
  by_cases h' : i < j
  · exact h i h'
  · have : i = j := by omega
    subst this; exact hj

theorem upto_zero {P : Nat → Bool} : ∀ i < 0, P i = true := fun _ h => absurd h (Nat.not_lt_zero _)

end QCert.QutritClifford
