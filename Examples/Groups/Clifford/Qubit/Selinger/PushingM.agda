------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): traversing the X-normal
-- staircase.
--
-- Pushing gives the rules for one dirty gate meeting one D or E box.
-- This module puts them together along a whole M(n), which is where the
-- staircase's shape starts to pay off.
--
-- The first result is the one the rest of the M side rests on: an S
-- entering at the bottom of a staircase walks straight up it to the E
-- box, changing nothing on the way.
--
--   altSIDD  S·D_ℓ = D_ℓ·S for all four D boxes, with the S moved from
--            the box's qubit 0 to its qubit 1 -- up one wire -- with no
--            phase and nothing else emitted.
--   altSE    S·E_h = E_{h+1}.
--
-- M(n)'s boxes sit on (0,1), (1,2), ..., so an S leaving one box at its
-- upper wire arrives at the next at its lower wire and the same rule
-- fires again; at the top it meets E.  So the traversal of the whole
-- staircase is: the E box advances by the number of S's, no D box
-- changes, no ω is produced and nothing escapes.
--
-- That is the whole reason the E box is where the paper puts it.  It
-- also settles, for this case, the invariant Tower flags -- that what
-- escapes a level must not touch the top wire -- because nothing
-- escapes at all: the S is absorbed by E, which is exactly the box
-- sitting on the top wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.PushingM
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Normal p-2 p-prime
  using (Mx)
open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using (Dirty ; H₀ ; S₀ ; X₀ ; H₁ ; S₁ ; X₁ ; H₂ ; S₂ ; ZZ₀₁ ; ZZ₁₂
        ; pushZZD)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The E box counts S gates
--
-- E₁, E₂, E₃, E₄ are ε, S, S², S³, so an S advances the box by one and
-- E₄ wraps to E₁.  This is altSE, read as a successor.

succE : EBox → EBox
succE e₁ = e₂
succE e₂ = e₃
succE e₃ = e₄
succE e₄ = e₁

stepE : ℕ → EBox → EBox
stepE 0       e = e
stepE (₁₊ k) e = stepE k (succE e)

------------------------------------------------------------------------
-- S gates entering the bottom of a staircase
--
-- Every D box passes the S on unchanged, so the recursion carries the
-- count up untouched and spends it all at the E box.  No phase, no
-- escaping dirt, and the D boxes are returned as they came.

pushS-Mx : ℕ → Mx n → Mx n
pushS-Mx {0}    k e       = stepE k e
pushS-Mx {₁₊ n} k (d , m) = d , pushS-Mx k m

-- The staircase of the identity -- all D₁ and E₁, as in (6.4) -- is
-- Tower.mx-id, and is not repeated here.  Pushing k S gates into it
-- returns it with E advanced, which is the M-side of the one-qubit
-- action generalised: at n = 0 this is exactly Rewrite's pushE.

------------------------------------------------------------------------
-- Splitting the dirt a D box emits
--
-- Which way a gate goes is decided by its subscript, and the rules make
-- the two directions completely different.
--
-- Subscript 1 is the box's UPPER wire, and the gate continues into the
-- rest of the staircase -- where it will meet the next box at ITS qubit
-- 0.  The only qubit-0 rule is altSIDD, which takes an S, so an S is the
-- only thing that can ascend; a D box that emitted an H upwards would
-- have nowhere to send it.  That is why ascending dirt is a COUNT.
--
-- Subscript 0 is the lower wire, below everything the staircase has
-- left, so those gates escape.  They are kept in order, as a word.

ascS : List Dirty → ℕ
ascS []          = 0
ascS (S₁ ∷ ds)  = ₁₊ (ascS ds)
ascS (_  ∷ ds)  = ascS ds

esc : List Dirty → List Dirty
esc []          = []
esc (H₀ ∷ ds)  = H₀ ∷ esc ds
esc (S₀ ∷ ds)  = S₀ ∷ esc ds
esc (X₀ ∷ ds)  = X₀ ∷ esc ds
esc (_  ∷ ds)  = esc ds

------------------------------------------------------------------------
-- A controlled-Z entering the bottom of a staircase
--
-- altZZDD rewrites the bottom D box and emits dirt on both its wires:
-- what goes up is S gates, which pushS-Mx carries to the E box, and
-- what stays escapes.  All four clauses are phase-free, so no ω is
-- produced.
--
-- D₁ and D₄ simply swap and emit nothing at all, which is the
-- controlled-Z analogue of the S case above.

pushZZ-Mx : Mx (₁₊ n) → List Dirty × Mx (₁₊ n)
pushZZ-Mx (d , m) with pushZZD d
... | _ , d′ , out = esc out , (d′ , pushS-Mx (ascS out) m)

------------------------------------------------------------------------
-- What cannot arrive
--
-- There is no rule for an H, or an X, meeting a D box at its qubit 0,
-- and the omission is not an oversight of the paper's: nothing ever
-- delivers one there.  Dirt reaches a staircase from the C box on its
-- left, and the C rules (commXC, commSC, commZZCI) emit only S gates
-- and controlled-Zs.  Both are handled above.
--
-- That is Definition 6.1's wire labelling doing its work: the wire a
-- staircase starts on admits S and controlled-Z as dirt, and not H or
-- X.  When h is assembled this has to become an invariant of the
-- traversal rather than a remark here.
