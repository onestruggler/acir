/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: normal forms

Definitions 4.6–4.9 of Makary, Ross and Selinger, in our wire numbering
(wire `0` at the bottom; the paper numbers qubits from the top).

* **Types** (Definition 4.6).  A wire is simple (`false`) or double (`true`).
  `A₁`, `A₂` leave a simple wire and `A₃` a double one; `B₁`–`B₄` take a
  simple lower wire and `B₅`–`B₈` a double one, and leave on the upper wire
  the same type, except `B₄` (simple to double) and `B₈` (double to simple);
  `C₁`, `C₂` take a simple wire; `D` and `E` are untyped.  `B_{j+5}` is the
  circuit `B_{j+1}` (`bB_idx`), so a `B` gate is given by its type and
  `j : Fin 4` (`bIdx`).
* A **Z-circuit** on `n` wires (Definition 4.7) acts on the top `m` wires,
  from the wire `a = n - m` up: `A_i` on the wire `a`, the ladder of `B`
  gates on `(a, a + 1), …, (n - 2, n - 1)`, then `C_k` on the wire `n - 1`,
  well typed: the wire `C` takes is simple (`ZNormal.ht`).
* An **X-circuit** (Definition 4.8) is `D_{ℓ₁}, …, D_{ℓ_{n-1}}` on the
  pairs `(n - 2, n - 1), …, (0, 1)`, then `E_h` on the wire `0`.
* A **normal** circuit (Definition 4.9) is `L M` followed by a normal
  circuit on the top `n - 1` wires, ending with a scalar `(-1)^p`.

All are read in time order, as in the paper's diagrams; box indices are
stored from `0`.
-/
import QCert.RealStabilizer.Boxes
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace QCert.RealStabilizer

/-- Wire types (Definition 4.6): `false` simple, `true` double. -/
abbrev Ty := Bool

/-- The type `A_{i+1}` leaves on its wire. -/
def tA : Fin 3 → Ty := ![false, false, true]

/-- The paper's index of the `B` gate `j` from a wire of type `t`: `B_{j+1}`
from a simple wire, `B_{j+5}` from a double one. -/
def bIdx (t : Ty) (j : Fin 4) : ℕ := j.val + 1 + (if t then 4 else 0)

/-- The type the `B` gate `j` leaves on its upper wire. -/
def tB (t : Ty) (j : Fin 4) : Ty := if j = 3 then !t else t

/-- The type at the top of a ladder of `B` gates. -/
def tBs : Ty → List (Fin 4) → Ty
  | t, [] => t
  | t, j :: js => tBs (tB t j) js

theorem bB_idx (t : Ty) (j : Fin 4) (c : ℕ) : bB (bIdx t j) c = bB (j.val + 1) c := by
  fin_cases j <;> cases t <;> rfl

/-- The ladder `B_{j₁} … B_{j_r}` from the wire `c` up, starting from a wire
of type `t`, then `C_{k+1}` on the top wire. -/
def BC : Ty → ℕ → List (Fin 4) → Fin 2 → List Lt
  | _, c, [], k => bC (k.val + 1) c
  | t, c, j :: js, k => bB (bIdx t j) c ++ BC (tB t j) (c + 1) js k

/-- The ladder `D_{ℓ₁} … D_{ℓ_r}` down to the wire `0`, then `E_{h+1}`. -/
def DC : List (Fin 4) → Fin 2 → List Lt
  | [], h => bE (h.val + 1) 0
  | l :: ls, h => bD (l.val + 1) ls.length ++ DC ls h

/-- A Z-circuit on `n` wires (Definition 4.7). -/
structure ZNormal (n : ℕ) where
  /-- The lowest wire the circuit acts on. -/
  a : ℕ
  i : Fin 3
  js : List (Fin 4)
  k : Fin 2
  h : a + js.length + 1 = n
  /-- Well typed: `C` takes a simple wire. -/
  ht : tBs (tA i) js = false

/-- An X-circuit on `n` wires (Definition 4.8). -/
structure XNormal (n : ℕ) where
  ls : List (Fin 4)
  h : Fin 2
  hl : ls.length + 1 = n

/-- The word of a Z-circuit, in time order. -/
def ZNormal.word {n : ℕ} (L : ZNormal n) : List Lt := bA (L.i.val + 1) L.a ++ BC (tA L.i) L.a L.js L.k

/-- The word of an X-circuit, in time order. -/
def XNormal.word {n : ℕ} (M : XNormal n) : List Lt := DC M.ls M.h

/-- Normal circuits (Definition 4.9): `L⁽ⁿ⁾ M⁽ⁿ⁾` followed by a normal circuit
on the top `n - 1` wires; on no wires, a scalar `(-1)^p`. -/
inductive NF : ℕ → Type
  | scalar (p : Fin 2) : NF 0
  | cons {n : ℕ} (L : ZNormal (n + 1)) (M : XNormal (n + 1)) (N : NF n) : NF (n + 1)

/-- The word of a normal circuit, in time order. -/
def NF.word : {n : ℕ} → NF n → List Lt
  | _, .scalar p => List.replicate p.val .neg
  | _, .cons L M N => L.word ++ M.word ++ N.word.map Lt.up

/-- The circuit of a normal form. -/
def NF.circ {n : ℕ} (N : NF n) : Circ n := wc n N.word

end QCert.RealStabilizer
