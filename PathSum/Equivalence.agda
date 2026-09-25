------------------------------------------------------------------------
-- Presentations of groups
--
-- Equivalence of two Clifford circuits, by reducing their miter
-- (Amy, QPL 2018, sections 3 and 4)
--
-- Section 4 says that "these heuristics combined with path-sum
-- reductions give a complete, polynomial-time procedure for
-- determining equivalence of Clifford group circuits", and section 3
-- says how: check that the miter is the identity.  For two circuits
-- over {H, S, CZ} the miter is itself a circuit, C₁ followed by C₂†
-- (PathSum.Miter's miter), so corollary 4.4 (PathSum.Corollary)
-- applies to it unchanged.  Take any reduction of the miter's
-- restricted path-sum that ends without path variables.  ⟦ C₁ ⟧ and
-- ⟦ C₂ ⟧ are equivalent exactly when it ends with no normalisation
-- left, the inputs as outputs (mod 2) and phase 0 (mod 2^M)
-- (equivalence-any).  So they are equivalent exactly when some
-- reduction ends that way (equivalence-syntactic).  Equivalence is
-- definition 2.3's: equality of the two operators, global phase
-- included, not equality up to a phase.
--
-- Not formalised: the polynomial time.  Decidability as such is
-- elementary, since a matrix has finitely many entries.
-- equivalence-decidable goes by the reduction, but its type does not
-- say so.  Checking a circuit against a general path-sum ξ is not
-- done this way either.  That miter, ⟦ C† ⟧ ∘ ξ, is a composition of
-- path-sums (definition 2.6), and deciding it by lemma 4.1 would also
-- need ξ to be well formed.  PathSum.Miter's spec-miter states only
-- the reduction to that miter, on columns.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Equivalence (M₀ : ℕ) where

open import Data.Integer.Base using (+_)
open import Data.List.Base using (_++_)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (trans to ⇔-trans)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (Dec; map′)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint M using (_†)
open import PathSum.Base using (PathSum; idPS; phase; out)
open import PathSum.Circuit M using (Circuit; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Corollary M₀ using
  (corollary-4-4-⟦⟧; corollary-4-4-any; corollary-4-4-syntactic;
   circuit-decidable)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Miter M₀ using (miter)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (_≈[_]_; μ; x[_]; 0ᴾ)
open import PathSum.Reduction M using (_⟶*_)

private
  variable
    n k′ : ℕ


------------------------------------------------------------------------
-- The verdict of a reduction of the miter

-- Either the miter's restricted path-sum reduces to one with no path
-- variables left, equivalent to the identity exactly when the two
-- circuits are equivalent, or the reduction has already told them
-- apart.

equivalence-⟦⟧ : (C₁ C₂ : Circuit n) →
  (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
     (⟦ C₁ ++ C₂ † ⟧ᴿ ⟶* ξ′) × (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivalence-⟦⟧ {n} C₁ C₂ = carry (corollary-4-4-⟦⟧ (C₁ ++ C₂ †))
  where
  carry : (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
             (⟦ C₁ ++ C₂ † ⟧ᴿ ⟶* ξ′) ×
             (⟦ C₁ ++ C₂ † ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
          ⊎ ¬ (⟦ C₁ ++ C₂ † ⟧ ≋ idPS) →
          (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
             (⟦ C₁ ++ C₂ † ⟧ᴿ ⟶* ξ′) × (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ξ′ ≋ idPS))
          ⊎ ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
  carry (inj₁ (k′ , ξ′ , steps , m⇔ξ′)) =
    inj₁ (k′ , ξ′ , steps , ⇔-trans (miter C₁ C₂) m⇔ξ′)
  carry (inj₂ ¬id) = inj₂ (λ eq → ¬id (Equivalence.to (miter C₁ C₂) eq))


------------------------------------------------------------------------
-- The end of the reduction, syntactically

-- Whatever chain from the miter's restricted path-sum ends without
-- path variables, the circuits are equivalent exactly when that
-- endpoint is syntactically |x⟩ ↦ |x⟩.

equivalence-any : (C₁ C₂ : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ⟶* ξ′ →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
equivalence-any C₁ C₂ steps =
  ⇔-trans (miter C₁ C₂) (corollary-4-4-any (C₁ ++ C₂ †) steps)

-- So the circuits are equivalent exactly when some such chain ends at
-- the identity's polynomials.

equivalence-syntactic : (C₁ C₂ : Circuit n) →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C₁ ++ C₂ † ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
equivalence-syntactic C₁ C₂ =
  ⇔-trans (miter C₁ C₂) (corollary-4-4-syntactic (C₁ ++ C₂ †))


------------------------------------------------------------------------
-- A decision procedure along that route

-- Decidability as such is elementary, and the type does not record
-- the route.

equivalence-decidable : (C₁ C₂ : Circuit n) → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivalence-decidable C₁ C₂ =
  map′ (Equivalence.from (miter C₁ C₂)) (Equivalence.to (miter C₁ C₂))
       (circuit-decidable (C₁ ++ C₂ †))
