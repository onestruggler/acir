------------------------------------------------------------------------
-- Presentations of groups
--
-- WellFormed is strictly weaker than definition 2.4: a tied witness
--
-- PathSum.PartialIsometry.Strict separates PathSum.Isometry's
-- WellFormed (every column of the operator has trace-form norm at most
-- 1) from definition 2.4 (the operator is a partial isometry) with
-- ½id = idᵏ 2 : PathSum 1 2 0, the identity with normalisation 1/2
-- and no path variables.  Definition 2.1 ties the normalisation to
-- the path variables, 1/√2^m with m of them, and with no path
-- variables that is 1: read as the paper reads a path-sum, ½id is the
-- identity, a partial isometry, and separates nothing.  So
-- WellFormed-strict separates the two notions on PathSum.Base's
-- path-sums, whose normalisation is free, and not yet on the paper's.
--
-- The witness here has the tie, PathSum 1 2 2.  It is idᵏ 1, the
-- identity with normalisation 1/√2, with PathSum.Tied's gadget added
-- (two more path variables, one more factor 1/√2, the same operator):
--
--    id√½ = |x⟩ ↦ 1/√2² Σ_{y₀y₁} e^{2πi(⅛y₀ - ⅛y₁ + ½y₀y₁)} |x⟩
--         = (1/√2)·I,
--
-- the sum being 1 + ζ^⅛ + ζ^-⅛ - 1 = √2 (amp-id√½).  Its columns have
-- norm 1/2, so it is WellFormed, and U†U = ½·I is not a projection, so
-- it is not a partial isometry (WellFormed-strict-tied).  Both facts
-- come from idᵏ 1 through id√½ ≋ idᵏ 1 (PathSum.Compose.WellFormed's
-- WellFormed-≋, PathSum.PartialIsometry's PartialIsometric-≋).  So
-- lemma 4.1 under WellFormed (PathSum.Isometry.lemma-4-1) is strictly
-- stronger than under definition 2.4 on path-sums in the paper's own
-- sense too.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.PartialIsometry.Strict.Tied (M₀ : ℕ) where

open import Data.Product.Base using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using (same)
open import PathSum.Base using (PathSum)
open import PathSum.Compose.WellFormed M₀ using (WellFormed-≋)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; √2·; √2·-map)
open import PathSum.Denotation M₀ using (amp; _≋_; ≋-sym)
open import PathSum.Hermitian M₀ using ([_]ᴬ)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.PartialIsometry M₀ using
  (PartialIsometric; PartialIsometric-≋)
open import PathSum.PartialIsometry.Strict M₀ using
  (idᵏ; amp-idᵏ; idᵏ-WellFormed; idᵏ-¬PartialIsometric)
open import PathSum.Tied M₀ using (gadget; gadget-≋; amp-gadget; move)

private
  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)


------------------------------------------------------------------------
-- (1/√2)·I with two path variables

id√½ : PathSum 1 2 2
id√½ = gadget (idᵏ {1} 1)

-- The equation along which facts about the gadget are moved; Agda
-- checks it on the path-sums, not on their amplitudes.

id√½-def : gadget (idᵏ {1} 1) ≡ id√½
id√½-def = refl

-- Its entries, unnormalised, are √2 on the diagonal and 0 off it.

amp-id√½ : ∀ x z → amp id√½ x z ≐ √2· [ same x z ]ᴬ
amp-id√½ = move (λ ξ → ∀ x z → amp ξ x z ≐ √2· [ same x z ]ᴬ)
                (gadget (idᵏ {1} 1)) id√½ id√½-def
  (λ x z → amp-gadget (idᵏ {1} 1) x z ∙ √2·-map (amp-idᵏ {1} 1 x z))

id√½≋idᵏ : id√½ ≋ idᵏ {1} 1
id√½≋idᵏ = move (λ ξ → ξ ≋ idᵏ {1} 1) (gadget (idᵏ {1} 1)) id√½ id√½-def
                (gadget-≋ (idᵏ {1} 1))


------------------------------------------------------------------------
-- Well-formed, but not a partial isometry

private
  ¬PI : ¬ PartialIsometric (idᵏ {1} 1)
  ¬PI = idᵏ-¬PartialIsometric 0

WellFormed-strict-tied :
  ∃ λ (ξ : PathSum 1 2 2) → WellFormed ξ × ¬ PartialIsometric ξ
WellFormed-strict-tied =
  id√½ ,
  WellFormed-≋ (idᵏ {1} 1) id√½
               (≋-sym {ξ = id√½} {ζ = idᵏ {1} 1} id√½≋idᵏ)
               (idᵏ-WellFormed {1} 1) ,
  (λ pi → ¬PI (PartialIsometric-≋ id√½ (idᵏ {1} 1) id√½≋idᵏ pi))

WellFormed⇏PartialIsometric-tied :
  ¬ (∀ (ξ : PathSum 1 2 2) → WellFormed ξ → PartialIsometric ξ)
WellFormed⇏PartialIsometric-tied h =
  ¬PI (PartialIsometric-≋ id√½ (idᵏ {1} 1) id√½≋idᵏ
        (h id√½ (WellFormed-≋ (idᵏ {1} 1) id√½
                   (≋-sym {ξ = id√½} {ζ = idᵏ {1} 1} id√½≋idᵏ)
                   (idᵏ-WellFormed {1} 1))))
