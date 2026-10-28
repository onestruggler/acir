/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The decision procedures of the rewriting engine

Toward Theorem 4.4.  The computational part of the engine
(`Engine.lean`, `Local.lean`), with no Mathlib import, so that the modules
deciding stored libraries (`Lib2Chk*`, ...) load nothing else:

* letters (`Lt`), their wires, canonical forms for commuting letters
  (`canon`), and runs of steps over a table of equations (`runStep`,
  `lemOk`, `libLemOk`);
* words and steps stored as numbers (`decW`, `decStep`, `decLib`);
* Pauli tableaux on one and two wires (`run1`, `run2`) and the free steps
  on two and three wires (`fo2`, `fo3`);
* the base tables (`base2`, `base3`) and inverse words (`invW`).

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

/-- The order of letters in canonical forms. -/
def rank : Lt → ℕ
  | H j => 3 * j
  | S j => 3 * j + 1
  | C j => 3 * j + 2

end Lt

/-- Wires `0`, `1`, `2` blocked by the letters passed so far. -/
structure Bl where
  b0 : Bool
  b1 : Bool
  b2 : Bool

namespace Bl

def get (bl : Bl) : ℕ → Bool
  | 0 => bl.b0
  | 1 => bl.b1
  | 2 => bl.b2
  | _ => true

/-- A letter is on wire `w`. -/
def onw (x : Lt) (w : ℕ) : Bool := x.lo ≤ w && w ≤ x.hi

def add (bl : Bl) (x : Lt) : Bl := ⟨bl.b0 || onw x 0, bl.b1 || onw x 1, bl.b2 || onw x 2⟩

/-- The letter may be moved in front of the letters passed. -/
def free (bl : Bl) (x : Lt) : Bool := !bl.get x.lo && !bl.get x.hi

end Bl

/-- Scan for the least-ranked letter that commutes with every letter before
it: `i` the position, `best` the best so far (position and letter). -/
def pickI : Bl → ℕ → Option (ℕ × Lt) → List Lt → Option (ℕ × Lt)
  | _, _, best, [] => best
  | bl, i, best, x :: rest =>
    let better : Bool := match best with
      | none => true
      | some (_, y) => decide (x.rank < y.rank)
    let best' := if (bl.free x && better) = true then some (i, x) else best
    pickI (bl.add x) (i + 1) best' rest

def pick (w : List Lt) : Option (List Lt × Lt × List Lt) :=
  match pickI ⟨false, false, false⟩ 0 none w with
  | none => none
  | some (i, x) => some (w.take i, x, w.drop (i + 1))

def canonF : ℕ → List Lt → List Lt
  | 0, w => w
  | n + 1, w => match pick w with
    | none => w
    | some (p, x, s) => x :: canonF n (p ++ s)

/-- The canonical form of a word for commuting letters on disjoint wires. -/
def canon (w : List Lt) : List Lt := canonF w.length w

/-- A step: an equation of the table at a place (`u`, `v`), reversed when
`rev`; or a free replacement of `s` by `t`. -/
inductive Step
  | rule (i : ℕ) (rev : Bool) (u v : List Lt)
  | free (u s t v : List Lt)
  | swaps (ps : List ℕ)

/-- Exchange the letters at positions `i`, `i + 1` when they are on disjoint wires. -/
def swapAt : ℕ → List Lt → Option (List Lt)
  | 0, x :: y :: r => if Lt.disj x y = true then some (y :: x :: r) else none
  | i + 1, x :: r => (swapAt i r).map (x :: ·)
  | _, _ => none

def swapsAt : List ℕ → List Lt → Option (List Lt)
  | [], w => some w
  | i :: ps, w => (swapAt i w).bind (swapsAt ps)

abbrev Tbl := List (List Lt × List Lt)

section Run

variable (fo : List Lt → List Lt → Bool)

def runStep (T : Tbl) (cur : List Lt) : Step → Option (List Lt)
  | .rule i rev u v => match T[i]? with
    | none => none
    | some e =>
      if (cur == u ++ (if rev then e.2 else e.1) ++ v ||
          canon cur == canon (u ++ (if rev then e.2 else e.1) ++ v)) = true
      then some (u ++ (if rev then e.1 else e.2) ++ v) else none
  | .free u s t v =>
    if ((cur == u ++ s ++ v || canon cur == canon (u ++ s ++ v)) && fo s t) = true
    then some (u ++ t ++ v) else none
  | .swaps ps => swapsAt ps cur

def runSteps (T : Tbl) : List Lt → List Step → Option (List Lt)
  | cur, [] => some cur
  | cur, st :: sts => match runStep fo T cur st with
    | none => none
    | some nxt => runSteps T nxt sts

def lemOk (T : Tbl) (l r : List Lt) (sts : List Step) : Bool :=
  match runSteps fo T l sts with
  | none => false
  | some c => c == r || canon c == canon r

/-- Check a library of lemmas, each over the table so far. -/
def libOk : Tbl → List (List Lt × List Lt × List Step) → Bool
  | _, [] => true
  | T, (l, r, sts) :: rest => lemOk fo T l r sts && libOk (T ++ [(l, r)]) rest

/-- The table after a library. -/
def libTbl (T : Tbl) (L : List (List Lt × List Lt × List Step)) : Tbl :=
  T ++ L.map fun e => (e.1, e.2.1)

end Run

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

def decPF : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 256 - 1) :: decPF f (n / 256)

/-- A list of positions stored as a number (base 256, digits shifted by one). -/
def decP (n : ℕ) : List ℕ := decPF 1000 n

/-- A stored step: `(0, i, rev, u, v)` a rule, `(1, u, s, t, v)` a free step,
`(2, ps, _, _, _)` swaps of adjacent commuting letters. -/
def decStep : ℕ × ℕ × ℕ × ℕ × ℕ → Step
  | (0, i, r, u, v) => .rule i (r == 1) (decW u) (decW v)
  | (1, u, s, t, v) => .free (decW u) (decW s) (decW t) (decW v)
  | (_, ps, _, _, _) => .swaps (decP ps)

/-- A stored library. -/
def decLib (L : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ))) :
    List (List Lt × List Lt × List Step) :=
  L.map fun e => (decW e.1, decW e.2.1, e.2.2.map decStep)

/-- Lemma `i` of a stored library checks over the table before it. -/
def libLemOk (fo : List Lt → List Lt → Bool) (B : Tbl)
    (D : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ))) (i : ℕ) : Bool :=
  match D[i]? with
  | none => false
  | some e => lemOk fo ((libTbl B (decLib D)).take (B.length + i)) (decW e.1) (decW e.2.1)
      (e.2.2.map decStep)

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
