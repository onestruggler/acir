------------------------------------------------------------------------
-- Presentations of groups
--
-- The uniform semantics of the Clifford+T family: Uₙ(𝔻[ω])
--
-- The unitary n × n matrices over 𝔻[ω] = ℤ[1/√2, i] (UMat n), equal
-- when their entries are (_≈ᵁ_).  The groups of the Clifford+T family
-- — over ℤ[½], ℤ[½, i], ℤ[1/√2] and ℤ[1/√2, i] — are all read there
-- (the DOmega modules of their developments, through Subring), so the
-- MainTheorem module of each development states its completeness and
-- soundness for this one relation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary where

open import Algebra.Bundles using (Group)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics public using (UMat)

infix 4 _≈ᵁ_

_≈ᵁ_ : ∀ {N} → UMat N → UMat N → Set
_≈ᵁ_ {N} = Group._≈_ (U N)
