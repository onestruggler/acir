------------------------------------------------------------------------
-- Presentations of groups
--
-- The alternating group 𝔄₁₆ as reversible circuits on four wires: the
-- gates X, CX, CCX and Ex, the cycles Ω 0, …, Ω 13, and the relations
-- that Lafont's presentation of 𝔄₁₆ translates into
--
-- The circuits on four wires over NOT, CNOT and Toffoli, with the swap
-- of two adjacent wires as a fourth gate, carry out exactly the even
-- permutations of the sixteen states of the wires.  Lafont's Theorem 4
-- (Examples.Groups.Alternating) presents the even permutations of
-- sixteen points by the fourteen cycles ω₀, …, ω₁₃, where ωᵢ sends i to
-- i + 1, i + 1 to i + 2 and i + 2 to i.  This module is the circuits'
-- side of a Reidemeister–Schreier step from that presentation, of the
-- kind Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Iso is.  The
-- generators are translated in both directions (Translation): each ωᵢ
-- is read as a circuit Ω i, and each gate as a word in the ωᵢ.  The
-- relations are translated: the rules below are Lafont's, read between
-- the Ω i, and one for each gate, which says which word in the Ω i the
-- gate is.  And the two sets of relations are proved equivalent (Iso):
-- each translation carries the relations of its source to consequences
-- of the relations of its target, so the circuits modulo these rules
-- and Lafont's words modulo his are isomorphic groups.
--
-- States.  A state is a vector of four bits, the bit of wire 0 first.
-- The sixteen states are numbered along the reflected Gray code, wire
-- 0 changing most often; written with wire 3 first,
--
--   0 0000    4 0110     8 1100    12 1010
--   1 0001    5 0111     9 1101    13 1011
--   2 0011    6 0101    10 1111    14 1001
--   3 0010    7 0100    11 1110    15 1000
--
-- Two consecutive states differ on one wire, so the states i, i + 1
-- and i + 2 are three corners of a face of the 4-cube, the other two
-- wires fixed, and the cycle of them is a doubly controlled cycle of
-- three states of two wires: the commutator of two Toffoli gates.
--
-- Wires and order.  Wire 0 is the bottom wire.  CX has its control on
-- wire 1 and its target on wire 0, CCX its controls on wires 1 and 2
-- and its target on wire 0, and Ex swaps the wires 0 and 1; w ↑ is w
-- one wire up.  Words are in diagram order: w • v is w followed by v.
--
-- The swap is structural: Ex is the designated swap of Circuit.Prop.
-- The relation _VRel,_===_ consists of the rules below (an instance r
-- is srel (srel r)), the laws of the symmetry (srel (σrel s): the swap
-- is an involution, and natural in every gate) and the structural rules
-- of Circuit.Base.  Naturality is why the rules gate-X, gate-CX and
-- gate-CCX, for the gates on the bottom wires, are enough: a gate on
-- other wires is that gate between swaps.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Syntactics where

open import Data.Nat using (ℕ ; _+_ ; _≤_)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates

data Gate : ℕ → Set where
  X-gate           : Gate 1
  CX-gate Ex-gate  : Gate 2
  CCX-gate         : Gate 3

open import Circuit.Prop Gate Ex-gate public

pattern X-gen   = gate₁ X-gate
pattern CX-gen  = gate₂ CX-gate
pattern Ex-gen  = gate₂ Ex-gate
pattern CCX-gen = gate₃ CCX-gate

-- The generators as one-letter circuits.  Ex is Circuit.Prop's σ.
X : Circuit (₁₊ n)
X = [ X-gen ]ʷ

CX Ex : Circuit (₂₊ n)
CX = [ CX-gen ]ʷ
Ex = [ Ex-gen ]ʷ

CCX : Circuit (₃₊ n)
CCX = [ CCX-gen ]ʷ

------------------------------------------------------------------------
-- NOT and the swap on each wire of four

X₀ X₁ X₂ X₃ : Circuit 4
X₀ = X
X₁ = X ↑
X₂ = X ↑ ↑
X₃ = X ↑ ↑ ↑

Ex₀ Ex₁ Ex₂ : Circuit 4
Ex₀ = Ex
Ex₁ = Ex ↑
Ex₂ = Ex ↑ ↑

------------------------------------------------------------------------
-- The cycle on a face
--
-- Between the swaps of the wires 0 1 and 2 3 the Toffoli gate has its
-- target on wire 1 and its controls on wires 0 and 3, so the square of
-- Ex₀ • Ex₂ • CCX is that gate followed by CCX, and its fourth power is
-- the commutator of the two.  With the wires 2 and 3 set it cycles the
-- states 01, 11, 10 of the wires 1 0, and it does nothing otherwise: K
-- is the cycle of the states 9, 10 and 11.

K : Circuit 4
K = (Ex₀ • Ex₂ • CCX) ^ 4

-- K on the other faces.  Kₐᵦ cycles x, x + eₐ and x + eₐ + eᵦ, where x
-- is the state with wire a clear and the other three wires set: K₁₀ is
-- K, and swaps carry it to the other pairs of wires.
K₁₀ K₀₁ K₂₀ K₀₂ K₃₀ K₀₃ : Circuit 4
K₁₀ = K
K₀₁ = Ex₀ • K₁₀ • Ex₀
K₂₀ = Ex₁ • K₁₀ • Ex₁
K₀₂ = Ex₁ • K₀₁ • Ex₁
K₃₀ = Ex₂ • K₂₀ • Ex₂
K₀₃ = Ex₂ • K₀₂ • Ex₂

------------------------------------------------------------------------
-- The cycles of three consecutive states
--
-- Ω i cycles the states i, i + 1 and i + 2.  If wire a changes from
-- state i to state i + 1, and wire b from i + 1 to i + 2, it is Kₐᵦ
-- between NOT gates on the wires where state i differs from the first
-- state of Kₐᵦ.  Beyond 13 there is no cycle, and Ω is ε.

Ω : ℕ → Circuit 4
Ω 0  = X₁ • X₂ • X₃ • K₀₁ • X₃ • X₂ • X₁
Ω 1  = X₂ • X₃ • K₁₀ • X₃ • X₂
Ω 2  = X₀ • X₂ • X₃ • K₀₂ • X₃ • X₂ • X₀
Ω 3  = X₀ • X₃ • K₂₀ • X₃ • X₀
Ω 4  = X₃ • K₀₁ • X₃
Ω 5  = X₁ • X₃ • K₁₀ • X₃ • X₁
Ω 6  = X₀ • X₁ • X₃ • K₀₃ • X₃ • X₁ • X₀
Ω 7  = X₀ • X₁ • K₃₀ • X₁ • X₀
Ω 8  = X₁ • K₀₁ • X₁
Ω 9  = K₁₀
Ω 10 = X₀ • K₀₂ • X₀
Ω 11 = X₀ • X₂ • K₂₀ • X₂ • X₀
Ω 12 = X₂ • K₀₁ • X₂
Ω 13 = X₁ • X₂ • K₁₀ • X₂ • X₁
Ω _  = ε

------------------------------------------------------------------------
-- The relations
--
-- order, near and far are the relations of Lafont's Theorem 4, and
-- apart his commutation of two cycles three or more points apart (the
-- structural rule comm₃ of his circuits), each at every position among
-- sixteen points.  The other six say which permutation of the states
-- each gate is, as a word in the cycles: the double transposition
-- (i i+1)(i+2 i+3) is Ω (1 + i) • Ω i, NOT on wire 0 exchanges the
-- states 2 i and 2 i + 1, and so on.  The word for Ex₂ has one letter
-- for every two inversions of its permutation, the fewest possible.

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → CRel n where

  -- Lafont's relations between the cycles.
  order : ∀ i → i ≤ 13 → 4 SRel, Ω i • Ω i • Ω i === ε
  near  : ∀ i → i ≤ 12 →
          4 SRel, Ω i • Ω (1 + i) • Ω i === Ω (1 + i) • Ω (1 + i)
  far   : ∀ i → i ≤ 11 →
          4 SRel, Ω i • Ω (2 + i) • Ω i === Ω (2 + i) • Ω i • Ω (1 + i)
  apart : ∀ i j → 3 + i ≤ j → j ≤ 13 →
          4 SRel, Ω j • Ω i === Ω i • Ω j

  -- The gates as words in the cycles.
  gate-X   : 4 SRel, X₀ ===
             Ω 1 • Ω 0 • Ω 5 • Ω 4 • Ω 9 • Ω 8 • Ω 13 • Ω 12
  gate-CX  : 4 SRel, CX === Ω 3 • Ω 2 • Ω 11 • Ω 10
  gate-CCX : 4 SRel, CCX === Ω 5 • Ω 4 • Ω 7 • Ω 6 • Ω 9 • Ω 8
  gate-Ex₀ : 4 SRel, Ex₀ ===
             Ω 1 • Ω 3 • Ω 2 • Ω 4 • Ω 9 • Ω 11 • Ω 10 • Ω 12
  gate-Ex₁ : 4 SRel, Ex₁ ===
             Ω 2 • Ω 3 • Ω 4 • Ω 2 • Ω 5 • Ω 3 •
             Ω 8 • Ω 9 • Ω 10 • Ω 8 • Ω 11 • Ω 9
  gate-Ex₂ : 4 SRel, Ex₂ ===
             Ω 6 • Ω 7 • Ω 8 • Ω 9 • Ω 10 • Ω 11 • Ω 12 • Ω 13 •
             Ω 4 • Ω 5 • Ω 6 • Ω 7 • Ω 8 • Ω 9 • Ω 10 • Ω 11 •
             Ω 6 • Ω 7 • Ω 8 • Ω 9 • Ω 4 • Ω 5 • Ω 6 • Ω 7

------------------------------------------------------------------------
-- The relation, with the swap rules and the structural rules

open Lift-To-Prop _SRel,_===_ public
