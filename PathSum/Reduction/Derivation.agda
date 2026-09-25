------------------------------------------------------------------------
-- Presentations of groups
--
-- Derivations as the paper writes them: rules and algebraic
-- manipulations
--
-- The worked examples of Amy's paper (QPL 2018) are displayed as a
-- column of path-sums, each line obtained from the one above "with the
-- following sequence of reductions and algebraic manipulations"
-- (example 3.3): a line is either a rule of figure 2 applied to the
-- line above, or the same path-sum with its phase polynomial rewritten
-- -- factored, or simplified modulo 1.  A Derivation is such a column.
-- Its steps are the general rules (PathSum.Reduction.General, which
-- embeds the linear ones) and syntactic congruences (Congruent, from
-- PathSum.Congruence: outputs equal modulo 2 and phase modulo 1,
-- coefficient by coefficient, which by Möbius inversion is equality
-- of the functions the paper's polynomials denote).  Every line is a
-- path-sum written out in full, so a formal derivation can follow the
-- printed one line by line.
--
-- derivation-sound is proposition 3.1 for such columns: each rule is
-- sound (PathSum.Reduction.Sound) and so is each manipulation
-- (PathSum.Congruence.congruent-≋), so the first line is equivalent to
-- the last.  A manipulation is typically discharged by computation,
-- the step _≈⟨⟩_ taking the congruence as an implicit True argument.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Reduction.Derivation (M₀ : ℕ) where

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (True; toWitness)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum)
open import PathSum.Reduction.General M using (_⟶ᴳ_)
open import PathSum.Reduction.Sound M₀ using (⟶ᴳ-sound)
open import PathSum.Congruence M₀ using
  (Congruent; congruent?; congruent-≋)
open import PathSum.Denotation M₀ using (_≋_; ≋-refl; ≋-trans)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Derivations

infixr 2 _⟶⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_
infix  3 _∎

data Derivation {n : ℕ} : ∀ {k m k′ m′} →
                          PathSum n k m → PathSum n k′ m′ → Set where

  _∎     : ∀ {k m} (ξ : PathSum n k m) → Derivation ξ ξ

  -- A rule of figure 2.
  _⟶⟨_⟩_ : ∀ {k m k′ m′ k″ m″} (ξ : PathSum n k m)
           {ζ : PathSum n k′ m′} {χ : PathSum n k″ m″} →
           ξ ⟶ᴳ ζ → Derivation ζ χ → Derivation ξ χ

  -- An algebraic manipulation: the next line is the same path-sum.
  _≈⟨_⟩_ : ∀ {k m k″ m″} (ξ : PathSum n k m)
           {ζ : PathSum n k m} {χ : PathSum n k″ m″} →
           Congruent ξ ζ → Derivation ζ χ → Derivation ξ χ

-- A manipulation checked by computation: the congruence is an implicit
-- True argument, which Agda fills in once the next line is known.

_≈⟨⟩_ : ∀ {k m k″ m″} (ξ : PathSum n k m) {ζ : PathSum n k m}
        {χ : PathSum n k″ m″} → Derivation ζ χ →
        {True (congruent? ξ ζ)} → Derivation ξ χ
_≈⟨⟩_ ξ {ζ} d {t} = ξ ≈⟨ toWitness {a? = congruent? ξ ζ} t ⟩ d


------------------------------------------------------------------------
-- Proposition 3.1 along a derivation

derivation-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
                   Derivation ξ ζ → ξ ≋ ζ
derivation-sound (ξ ∎) = ≋-refl {ξ = ξ}
derivation-sound (_⟶⟨_⟩_ ξ {ζ} {χ} s d) =
  ≋-trans {ξ = ξ} {ζ = ζ} {χ = χ} (⟶ᴳ-sound s) (derivation-sound d)
derivation-sound (_≈⟨_⟩_ ξ {ζ} {χ} c d) =
  ≋-trans {ξ = ξ} {ζ = ζ} {χ = χ} (congruent-≋ ξ ζ refl c)
          (derivation-sound d)
