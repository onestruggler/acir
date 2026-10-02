------------------------------------------------------------------------
-- Presentations of groups
--
-- At order 3 the linear rules are not all of figure 2
--
-- PathSum.Full.Order2 proves that a path-sum whose phase has order at
-- most 2 and to which no linear rule of figure 2 (Amy, QPL 2018)
-- applies -- [Elim], or [ω] or [HH] with a Z₂-linear quotient, at any
-- path variable -- is irreducible under all of figure 2.  This module
-- shows that the order bound cannot be raised to 3, at precision M = 3.
--
-- The witness is PathSum.Cost.Excluded's ξᴱ: inputs x₀, x₁, path
-- variables y₀, y₁, identity outputs, normalisation 0 and phase
--
--    ½ y₀y₁ + ½ y₀x₀x₁ + ⅛ y₁ ,
--
-- of order 3.  Its path variables are internal (ξᴱ-internal).  No
-- linear rule applies to it at any variable (ξᴱ-irreducible, decided by
-- PathSum.Anywhere.Match's search): with normalisation 0 only [HH]
-- could, its quotient by y₀ has the coefficient ½ at x₀x₁, which no
-- ½-multiple of a lifted linear form has, and its quotient by y₁ has
-- the constant coefficient ⅛.  But figure 2's [HH] at y₀ with the
-- Boolean-valued quotient x₀x₁ applies (PathSum.Cost.Excluded.
-- full-step), so ξᴱ is not irreducible under _⟶ᶠ_
-- (ξᴱ-not-irreducibleᶠ).  The same polynomials do the same at every
-- M ≥ 3 (stated here, proved at M = 3 only).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Full.Order2.Sharp where

open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Anywhere.Match 3 using (Irreducible; irreducible?; NoVar?)
open import PathSum.Base using (PathSum; phase; out; Internal)
open import PathSum.Cost.Excluded using (ξᴱ; full-step; order-before)
open import PathSum.Full.Match 3 using (Irreducibleᶠ)
open import PathSum.Order 3 using (Ord≤)
open import PathSum.Polynomial using (y[_])


------------------------------------------------------------------------
-- The witness

-- Its path variables are internal ...

ξᴱ-internal : Internal ξᴱ
ξᴱ-internal = toWitness
  {a? = all? (λ j → all? (λ w → NoVar? (+ 2) y[ j ] (out ξᴱ w)))} _

-- ... no linear rule applies to it ...

ξᴱ-irreducible : Irreducible ξᴱ
ξᴱ-irreducible = toWitness {a? = irreducible? ξᴱ} _

-- ... but a rule of figure 2 does.

ξᴱ-not-irreducibleᶠ : ¬ Irreducibleᶠ ξᴱ
ξᴱ-not-irreducibleᶠ irr = irr full-step

-- So "linearly irreducible implies irreducible under figure 2" fails at
-- order 3, even with internal path variables.

order-3-gap : Σ (PathSum 2 0 2) λ ξ →
              Ord≤ 3 (phase ξ) × Internal ξ × Irreducible ξ ×
              ¬ Irreducibleᶠ ξ
order-3-gap =
  ξᴱ , order-before , ξᴱ-internal , ξᴱ-irreducible , ξᴱ-not-irreducibleᶠ
