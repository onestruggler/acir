------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.1 needs well-formedness (Amy, QPL 2018, section 4.1)
--
-- Lemma 4.1 says that a well-formed path-sum is the identity exactly
-- when its isometry restriction is, and section 4.1 remarks that the
-- hypothesis is needed: "U_ξ|x⟩ = |x⟩ + |ψ⟩ for some residual state
-- |ψ⟩" can have the restriction of the identity without being it.
-- PathSum.Isometry proves the lemma (lemma-4-1, under WellFormed);
-- this module checks the remark, with |ψ⟩ = |x ⊕ 1⟩ on one qubit.
--
--    dup = |x⟩ ↦ Σ_{y₀} |y₀⟩ = |0⟩ + |1⟩ = |x⟩ + |x ⊕ 1⟩
--
-- (PathSum.Compose.Counterexample's toY 0: phase 0, output y₀,
-- normalisation 1, every entry ζ⁰.)  Its restriction is the identity,
-- the one path from x to x having phase 0 (dup-restriction), but its
-- entry from x to x ⊕ 1 is 1 where the identity's is 0 (dup-not-id).
-- By lemma 4.1 it is not WellFormed (dup-¬WellFormed): its columns have
-- norm 2.
--
-- dup is not a path-sum of definition 2.1, which ties the
-- normalisation to the path variables: with one path variable it is
-- 1/√2, and |x⟩ ↦ 1/√2 Σ_{y₀} |y₀⟩ has diagonal entries 1/√2, so its
-- restriction is not the identity and it refutes nothing.  The tied
-- witness is dup with PathSum.Tied's pad added (one more path variable
-- occurring nowhere, one more factor 1/2, the same operator):
--
--    dupᵗ = |x⟩ ↦ 1/√2² Σ_{y₀y₁} |y₁⟩ = |x⟩ + |x ⊕ 1⟩,
--
-- a PathSum 1 2 2.  The restriction condition, being the identity and
-- WellFormed are all properties of the operator (PathSum.Tied's
-- Restriction-id-≋, ≋-trans, PathSum.Compose.WellFormed's
-- WellFormed-≋), so dupᵗ ≋ dup carries the three facts across
-- (lemma-4-1-needs-WellFormed-tied).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Isometry.Counterexample (M₀ : ℕ) where

open import Data.Bool.Base using (true; false)
open import Data.Integer.Base using (0ℤ)
open import Data.Product.Base using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum; idPS)
open import PathSum.Compose.Counterexample M₀ using (toY; amp-toY)
open import PathSum.Compose.WellFormed M₀ using (WellFormed-≋)
open import PathSum.Cyclotomic M₀ using (0ᴬ; _≐_; zpow; zpow-0≢0ᴬ)
open import PathSum.Denotation M₀ using
  (Assign; amp; _≋_; ≋-sym; ≋-trans)
open import PathSum.Isometry M₀ using
  (WellFormed; Restriction-id; lemma-4-1⇐; amp-no-path; idPS-diagonal)
open import PathSum.Tied M₀ using (pad; pad-≋; Restriction-id-≋; move)


------------------------------------------------------------------------
-- |x⟩ ↦ |x⟩ + |x ⊕ 1⟩

dup : PathSum 1 0 1
dup = toY 0

-- The equation along which facts about toY 0 are moved; Agda checks it
-- on the path-sums, not on their amplitudes.

dup-def : toY 0 ≡ dup
dup-def = refl

-- Every entry is ζ⁰.

amp-dup : ∀ x z → amp dup x z ≐ zpow 0ℤ
amp-dup = move (λ ξ → ∀ x z → amp ξ x z ≐ zpow 0ℤ) (toY 0) dup dup-def
               (amp-toY 0)

-- The restriction is the identity.

dup-restriction : Restriction-id dup
dup-restriction x = amp-dup x x

-- The entry from 0 to 1 is ζ⁰, where the identity's is 0.

dup-not-id : ¬ (dup ≋ idPS)
dup-not-id e = zpow-0≢0ᴬ (λ i →
  trans (sym (amp-dup x₀ x₁ i)) (trans (e x₀ x₁ i) (off i)))
  where
  x₀ x₁ : Assign 1
  x₀ _ = false
  x₁ _ = true

  off : amp idPS x₀ x₁ ≐ 0ᴬ
  off = amp-no-path idPS x₀ x₁ (λ y → idPS-diagonal x₀ y x₁) refl

-- So dup is not WellFormed, or lemma 4.1 would make it the identity.

dup-¬WellFormed : ¬ WellFormed dup
dup-¬WellFormed wf = dup-not-id (lemma-4-1⇐ dup wf dup-restriction)

lemma-4-1-needs-WellFormed :
  ∃ λ (ξ : PathSum 1 0 1) → Restriction-id ξ × ¬ (ξ ≋ idPS)
lemma-4-1-needs-WellFormed = dup , dup-restriction , dup-not-id


------------------------------------------------------------------------
-- The tied witness

dupᵗ : PathSum 1 2 2
dupᵗ = pad dup

dupᵗ-def : pad dup ≡ dupᵗ
dupᵗ-def = refl

dupᵗ≋dup : dupᵗ ≋ dup
dupᵗ≋dup = move (λ ξ → ξ ≋ dup) (pad dup) dupᵗ dupᵗ-def (pad-≋ dup)

private
  dup≋dupᵗ : dup ≋ dupᵗ
  dup≋dupᵗ = ≋-sym {ξ = dupᵗ} {ζ = dup} dupᵗ≋dup

dupᵗ-restriction : Restriction-id dupᵗ
dupᵗ-restriction = Restriction-id-≋ dup dupᵗ dup≋dupᵗ dup-restriction

dupᵗ-not-id : ¬ (dupᵗ ≋ idPS)
dupᵗ-not-id e =
  dup-not-id (≋-trans {ξ = dup} {ζ = dupᵗ} {χ = idPS} dup≋dupᵗ e)

dupᵗ-¬WellFormed : ¬ WellFormed dupᵗ
dupᵗ-¬WellFormed wf = dup-¬WellFormed (WellFormed-≋ dupᵗ dup dupᵗ≋dup wf)

lemma-4-1-needs-WellFormed-tied :
  ∃ λ (ξ : PathSum 1 2 2) → Restriction-id ξ × ¬ (ξ ≋ idPS)
lemma-4-1-needs-WellFormed-tied = dupᵗ , dupᵗ-restriction , dupᵗ-not-id
