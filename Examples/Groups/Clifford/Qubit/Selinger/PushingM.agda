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
open import ForStdlib.Data.Fin.Mod using (ℤ)

open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using (Dirty ; H₀ ; S₀ ; X₀ ; H₁ ; S₁ ; X₁ ; H₂ ; S₂ ; ZZ₀₁ ; ZZ₁₂
        ; pushZZD ; pushS₁D ; pushH₁D)

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

-- Every constructor is listed rather than caught by a wildcard.  The D
-- rules emit only H₀, S₀ and S₁ -- checked against all sixteen clauses
-- of altIHDD, altISDD, altSIDD and altZZDD -- so the other seven cases
-- cannot arise; but a wildcard would DROP one silently if a rule were
-- ever mistranscribed, and dropping a gate is a soundness bug that
-- nothing here would catch.  Written out, a surprise shows up instead
-- as a clause that is visibly wrong.

ascS : List Dirty → ℕ
ascS []         = 0
ascS (S₁ ∷ ds) = ₁₊ (ascS ds)
-- escaping, counted by esc
ascS (H₀ ∷ ds) = ascS ds
ascS (S₀ ∷ ds) = ascS ds
ascS (X₀ ∷ ds) = ascS ds
-- not emitted by any D rule
ascS (H₁ ∷ ds) = ascS ds
ascS (X₁ ∷ ds) = ascS ds
ascS (H₂ ∷ ds) = ascS ds
ascS (S₂ ∷ ds) = ascS ds
ascS (ZZ₀₁ ∷ ds) = ascS ds
ascS (ZZ₁₂ ∷ ds) = ascS ds

esc : List Dirty → List Dirty
esc []         = []
esc (H₀ ∷ ds) = H₀ ∷ esc ds
esc (S₀ ∷ ds) = S₀ ∷ esc ds
esc (X₀ ∷ ds) = X₀ ∷ esc ds
-- ascending, counted by ascS
esc (S₁ ∷ ds) = esc ds
-- not emitted by any D rule
esc (H₁ ∷ ds) = esc ds
esc (X₁ ∷ ds) = esc ds
esc (H₂ ∷ ds) = esc ds
esc (S₂ ∷ ds) = esc ds
esc (ZZ₀₁ ∷ ds) = esc ds
esc (ZZ₁₂ ∷ ds) = esc ds

------------------------------------------------------------------------
-- A dirty gate meeting the bottom box of a staircase
--
-- All four D families have the same shape once the split above is in
-- place: rewrite the bottom box by the rule, carry the ascending S
-- gates to the E box with pushS-Mx, and hand back what escapes.  The
-- rule is the only thing that differs, so it is a parameter.
--
-- The phase is returned rather than dropped even though every D rule is
-- phase-free, so that the caller is not relying on that.

push-bottom : (DBox → ℤ 8 × DBox × List Dirty) →
              Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
push-bottom rule (d , m) with rule d
... | k , d′ , out = k , esc out , (d′ , pushS-Mx (ascS out) m)

-- A controlled-Z on the staircase's bottom pair (altZZDD).  D₁ and D₄
-- simply swap and emit nothing at all.
pushZZ-Mx : Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
pushZZ-Mx = push-bottom pushZZD

-- An S arriving on the upper wire of the bottom box (altISDD).  This is
-- what a C₂ box sends into the staircase, via commZZCI's trailing S
-- gates.
pushS₁-Mx : Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
pushS₁-Mx = push-bottom pushS₁D

-- An H arriving on the upper wire of the bottom box (altIHDD).
pushH₁-Mx : Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
pushH₁-Mx = push-bottom pushH₁D

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
