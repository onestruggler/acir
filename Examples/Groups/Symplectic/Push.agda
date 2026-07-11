------------------------------------------------------------------------
-- Presentations of groups
--
-- Index of the coset-update "push" lemmas for the symplectic Clifford
-- normal form.  Pushing a generator g through an LM box is decomposed as
--
--     push g through the L box  →  read off the dirty gate  →
--     push the dirty gate through the M column.
--
-- The dirty gates an L-push can emit are built only from {S, S↑, CZ} —
-- never a raw H (every A-box direction is a power of S; the B boxes add
-- S↑ and CZ).  So the M column never needs an H-through-M rule, which is
-- the hard case.  This module re-exports the pieces built so far.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Push (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

------------------------------------------------------------------------
-- Pushing a dirty gate through the M column  [ m ]ᵐ • dirty ≈ dir • [ m' ]ᵐ

-- S through M (general n).
open import Examples.Groups.Symplectic.PushM p-2 p-prime public
  using (push-M-S)

-- S^j through M (general n), by iterating push-M-S.
open import Examples.Groups.Symplectic.PushMSn p-2 p-prime public
  using (push-M-Sⁿ)

-- S↑ through M (base M 2), CZ through M (M 3), and the E box absorbing an
-- S-power.
open import Examples.Groups.Symplectic.PushMScz p-2 p-prime public
  using (push-M-S↑ ; push-M-CZ ; push-M-CZ-M2-a0 ; push-E-S^)

-- H through M — the assembly, parametric in the (still-open) D-box H-push.
open import Examples.Groups.Symplectic.PushMH p-2 p-prime public
  using (push-M-H)

-- The a = 0 rows of that D-box H-push.
open import Examples.Groups.Symplectic.Pushing.DHa0 p-2 p-prime public
  using (aux-DHa0)

------------------------------------------------------------------------
-- The LM-box push  [ lm ]ˡᵐ • [ g ]ʷ ≈ dir • [ lm' ]ˡᵐ

-- Width 1 (LM 1 = E · A): the full pipeline, everything absorbed.
open import Examples.Groups.Symplectic.PushLM1 p-2 p-prime public
  using (push-LM1)

-- Width 2, inj₂ shape (M · A, no B boxes): the dirty S^k escapes upward
-- through the M column.
open import Examples.Groups.Symplectic.PushLM2 p-2 p-prime public
  using (push-LM2-inj₂-S ; push-LM2-inj₂-H)
