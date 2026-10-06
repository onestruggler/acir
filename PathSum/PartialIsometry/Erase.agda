------------------------------------------------------------------------
-- Presentations of groups
--
-- |x⟩ ↦ |0⟩ is a path-sum, and it is not an isometry (Amy, QPL 2018,
-- section 2)
--
-- Section 2 of the paper remarks, just before definition 2.4, that
-- "non-isometric path-sums are possible in our framework, as for
-- instance |x⟩ ↦ |0⟩ is a valid path-sum".  That path-sum is
-- PathSum.Compose.Counterexample's erase: one input, phase 0, no path
-- variables, no normalisation, and the output polynomial 0.  It is a
-- path-sum in the sense of definition 2.1 as printed -- its
-- normalisation 1/√2^0 is tied to its number of path variables, 0 --
-- so nothing here depends on this development keeping the two apart.
--
-- Its operator sends both basis states to |0⟩, so U†U is the all-ones
-- matrix [[1,1],[1,1]], whose square is twice itself:
--
--   * U is not an isometry (erase-¬Isometric): U†U ≠ I;
--   * U is not even a partial isometry (erase-¬PartialIsometric):
--     (U†U)² ≠ U†U, so erase is not well formed in the sense of
--     definition 2.4 -- the paper's remark, in its strongest reading;
--   * yet every column has norm 1, so erase is WellFormed in the
--     weaker sense of PathSum.Isometry under which lemma 4.1 is proved
--     (erase-WellFormed).  So the paper's own example is a second
--     witness, beside PathSum.PartialIsometry.Strict's ½·id, that
--     WellFormed does not imply definition 2.4 -- and unlike ½·id it
--     has the normalisation definition 2.1 prescribes
--     (WellFormed⇏PartialIsometric-tied).
--
-- The integer arithmetic is PathSum.Compose.Counterexample's: erase's
-- amplitudes are integer multiples of ζ⁰ (real-erase), and definition
-- 2.4 reduces to a statement about the integer Gram matrix (real-PI⁻),
-- which fails at the input 0: (U†U)² has entry 2 there and U†U entry
-- 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.PartialIsometry.Erase (M₀ : ℕ) where

open import Data.Bool.Base using (false)
open import Data.Integer.Base using (+_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.Product.Base using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum)
open import PathSum.Compose.Counterexample M₀ using
  (erase; aᵉ; real-erase; real-WF; real-PI⁻)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.PartialIsometry M₀ using
  (Isometric; PartialIsometric; Isometric⇒PartialIsometric)


------------------------------------------------------------------------
-- The path-sum

-- |x⟩ ↦ |0⟩, with definition 2.1's normalisation: no path variable and
-- no factor 1/√2.

eraseᵖ : PathSum 1 0 0
eraseᵖ = erase


------------------------------------------------------------------------
-- Well formed in the weak sense

-- Every column has norm 1: the single path reaches |0⟩ with phase 0.

erase-WellFormed : WellFormed eraseᵖ
erase-WellFormed x = ≤-reflexive (real-WF erase aᵉ real-erase x)


------------------------------------------------------------------------
-- Not an isometry, nor a partial isometry

private
  2≢1 : + 2 ≢ + 1
  2≢1 ()

-- At the input 0: the square of the integer Gram matrix has entry 2,
-- the Gram matrix (times 2^0) entry 1.

erase-¬PartialIsometric : ¬ PartialIsometric eraseᵖ
erase-¬PartialIsometric pi = 2≢1 (real-PI⁻ erase aᵉ real-erase pi false false)

erase-¬Isometric : ¬ Isometric eraseᵖ
erase-¬Isometric iso =
  erase-¬PartialIsometric (Isometric⇒PartialIsometric erase iso)

-- The remark, with its strongest reading and the weak well-formedness
-- that still holds.

non-isometric-path-sum :
  WellFormed eraseᵖ × ¬ PartialIsometric eraseᵖ × ¬ Isometric eraseᵖ
non-isometric-path-sum =
  erase-WellFormed , erase-¬PartialIsometric , erase-¬Isometric

-- A witness, with the normalisation tied to the path variables as in
-- definition 2.1, that WellFormed does not imply definition 2.4.

WellFormed⇏PartialIsometric-tied :
  ∃ λ (ξ : PathSum 1 0 0) → WellFormed ξ × ¬ PartialIsometric ξ
WellFormed⇏PartialIsometric-tied =
  eraseᵖ , erase-WellFormed , erase-¬PartialIsometric
