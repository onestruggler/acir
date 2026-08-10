------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the symmetric group: bijections on Fin n via
-- Data.Fin.Permutation.Permutation′.
--
-- The tight semantic domain, and the one the presentation theorem
-- targets: unlike the endofunctions of SubPresentation.Semantics, every
-- permutation is a denotation (Surjectivity), so the sub-presentation
-- can be promoted to a presentation.
-- Re-exports the group structure on Permutation′ n (whose generic
-- definition lives in ForStdlib.Data.Fin.Permutation.Properties).
--
-- Nothing here mentions the syntax.  swap01 and shift are named after
-- the generators they will interpret, but they are permutations, not
-- denotations; the map from circuits to them is Interpretation, and
-- that it respects the relations is Soundness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Semantics where

open import Data.Fin using (Fin ; zero)
open import Data.Fin.Permutation using (Permutation′ ; permutation ; lift₀)
open import Data.Nat using (ℕ)
open import Notations using (₁₊ ; ₂₊)

import Relation.Binary.PropositionalEquality as Eq

open Eq using (refl)

------------------------------------------------------------------------
-- Permutation type

Perm : ℕ → Set
Perm n = Permutation′ n

------------------------------------------------------------------------
-- Group structure on Permutation′ n

-- The symmetric group Sₙ is a generic carrier: its construction lives
-- in the standard-library supplement (under the idiomatic name
-- ∘ₚ-id-group).  Re-exported here as Permutation′-group so that the
-- tight semantics keeps a single, readable home for "the meaning of
-- the syntax".
import ForStdlib.Data.Fin.Permutation.Properties as PermProperties

open PermProperties public
  using () renaming (∘ₚ-id-group to Permutation′-group)

------------------------------------------------------------------------
-- Semantic building blocks

-- The underlying function for swap01 (used to build the Permutation′).
private
  swap01-fun : ∀ {n} → Fin (₂₊ n) → Fin (₂₊ n)
  swap01-fun zero      = ₁₊ zero
  swap01-fun (₁₊ zero) = zero
  swap01-fun (₂₊ k)    = ₂₊ k

-- Swap positions 0 and 1: what σ-gate will denote.
swap01 : ∀ {n} → Perm (₂₊ n)
swap01 = permutation swap01-fun swap01-fun
  (λ { zero → refl ; (₁₊ zero) → refl ; (₂₊ _) → refl })
  (λ { zero → refl ; (₁₊ zero) → refl ; (₂₊ _) → refl })

-- Shift a permutation up by one wire: what _↥ will act as.
shift : ∀ {n} → Perm n → Perm (₁₊ n)
shift = lift₀
