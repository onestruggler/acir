------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.4 at a Clifford circuit (Amy, QPL 2018)
--
-- The circuit-level results that combine the modules below them:
-- lemma 4.1 at a circuit (its path-sum ⟦ C ⟧ against its reified
-- isometry restriction ⟦ C ⟧ᴿ), the verdict of a reduction carried back
-- to the circuit, and corollary 4.4 in the form its proof gives it --
-- whatever reduction of ⟦ C ⟧ᴿ ends without path variables, the
-- circuit is the identity exactly when that end is syntactically
-- |x⟩ ↦ |x⟩.  PathSum.Theorems restates everything here; the proofs
-- live in this module so that later developments can import them
-- without importing the root.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Corollary (M₀ : ℕ) where

open import Data.Integer.Base using (+_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans)
open import Relation.Nullary.Decidable using (Dec; no; map′)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Circuit M using (Circuit; norm; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Cyclotomic M₀ using (_≐_; scale; scale-map)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (μ; x[_]; 0ᴾ; _≈[_]_)
open import PathSum.Reduction M using (_⟶*_)

import PathSum.Circuit
module Circ = PathSum.Circuit M

import PathSum.Denotation
module Den = PathSum.Denotation M₀

open Den using (Assign; amp; _≋_; semantics)

import PathSum.Clifford
module Cliff = PathSum.Clifford M₀ semantics

import PathSum.Identity
module Idn = PathSum.Identity M₀

import PathSum.Isometry
module Isom = PathSum.Isometry M₀

open Isom using (WellFormed; Restriction-id)

import PathSum.CircuitAmp
module CAmp = PathSum.CircuitAmp M₀

import PathSum.CircuitSemantics
module CSem = PathSum.CircuitSemantics M₀

open CSem using (δ; applyᴬ)

import PathSum.Decide
module Dcd = PathSum.Decide M₀

import PathSum.Syntactic
module Syn = PathSum.Syntactic M₀

private
  variable
    n k′ : ℕ


------------------------------------------------------------------------
-- What "⟦ C ⟧ is the identity" means

-- The circuit's matrix, computed gate by gate, is the identity matrix.

circuit-≋-id : (C : Circuit n) →
               (⟦ C ⟧ ≋ idPS ⇔
                (∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z)))
circuit-≋-id C = mk⇔
  (λ eq x z i → trans (sym (CSem.prop-2-10 C x z i))
    (trans (eq x z i) (scale-map (norm C) (CAmp.ampˢ-init x z) i)))
  (λ eq x z i → trans (CSem.prop-2-10 C x z i)
    (trans (eq x z i) (sym (scale-map (norm C) (CAmp.ampˢ-init x z) i))))


------------------------------------------------------------------------
-- The hypotheses of corollary 4.4, and the corollary, at ⟦ C ⟧ᴿ

corollary-4-4-circuit : (C : Circuit n) → Cliff.Reduces ⟦ C ⟧ᴿ
corollary-4-4-circuit C =
  Cliff.corollary-4-4 ⟦ C ⟧ᴿ (Circ.⟦⟧ᴿ-Internal C) (Circ.⟦⟧ᴿ-Ord≤ C)


------------------------------------------------------------------------
-- Lemma 4.1 at a circuit

-- ⟦ C ⟧ satisfies WellFormed, and ⟦ C ⟧ᴿ is its isometry restriction,
-- reified: the two have the same diagonal, and no path of ⟦ C ⟧ᴿ
-- leaves its input.

circuit-WellFormed : (C : Circuit n) → WellFormed ⟦ C ⟧
circuit-WellFormed C x = ≤-reflexive (CSem.⟦⟧-unit-columns C x)

lemma-4-1-circuit : (C : Circuit n) → (⟦ C ⟧ ≋ idPS ⇔ ⟦ C ⟧ᴿ ≋ idPS)
lemma-4-1-circuit C = mk⇔ to from
  where
  whole : ⟦ C ⟧ ≋ idPS ⇔ Restriction-id ⟦ C ⟧
  whole = Isom.lemma-4-1 ⟦ C ⟧ (circuit-WellFormed C)

  restricted : ⟦ C ⟧ᴿ ≋ idPS ⇔ Restriction-id ⟦ C ⟧ᴿ
  restricted = Isom.diagonal-≋ ⟦ C ⟧ᴿ (CSem.⟦⟧ᴿ-diagonal C)

  to : ⟦ C ⟧ ≋ idPS → ⟦ C ⟧ᴿ ≋ idPS
  to eq = Equivalence.from restricted (λ x i →
    trans (CSem.⟦⟧ᴿ-restricts C x i) (Equivalence.to whole eq x i))

  from : ⟦ C ⟧ᴿ ≋ idPS → ⟦ C ⟧ ≋ idPS
  from eq = Equivalence.from whole (λ x i →
    trans (sym (CSem.⟦⟧ᴿ-restricts C x i))
          (Equivalence.to restricted eq x i))


------------------------------------------------------------------------
-- The verdict, transported back to the circuit

-- A reduct is equivalent to ⟦ C ⟧ᴿ (proposition 3.1 along the chain),
-- and lemma 4.1 at the circuit carries that to ⟦ C ⟧.

reduct≋ : (C : Circuit n) {ξ′ : PathSum n k′ 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
          (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
reduct≋ C {ξ′ = ξ′} steps = mk⇔
  (λ eq → Den.≋-trans {ξ = ξ′} {ζ = ⟦ C ⟧ᴿ} {χ = idPS}
            (Den.≋-sym {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} (Cliff.⟶*-sound steps))
            (Equivalence.to (lemma-4-1-circuit C) eq))
  (λ eq → Equivalence.from (lemma-4-1-circuit C)
            (Den.≋-trans {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} {χ = idPS}
                         (Cliff.⟶*-sound steps) eq))

circuit-id : (C : Circuit n) {ξ′ : PathSum n 0 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
             (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) →
             phase ξ′ ≈[ pow M ] 0ᴾ →
             ⟦ C ⟧ ≋ idPS
circuit-id C {ξ′} steps eqf eqP =
  Equivalence.from (reduct≋ C steps) (Idn.id-if ξ′ eqf eqP)

circuit-not-id : (C : Circuit n) {ξ′ : PathSum n k′ 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
                 ¬ (ξ′ ≋ idPS) → ¬ (⟦ C ⟧ ≋ idPS)
circuit-not-id C steps ¬id C≋id =
  ¬id (Equivalence.to (reduct≋ C steps) C≋id)

-- Either ⟦ C ⟧ᴿ reduces to a path-sum with no path variables left,
-- whose being the identity is exactly the circuit's, or the reduction
-- has already refuted the circuit.

corollary-4-4-⟦⟧ : (C : Circuit n) →
  (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
     (⟦ C ⟧ᴿ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C ⟧ ≋ idPS)
corollary-4-4-⟦⟧ C with corollary-4-4-circuit C
... | Cliff.done {ξ′ = ξ′} steps = inj₁ (_ , ξ′ , steps , reduct≋ C steps)
... | Cliff.no-id ¬id =
  inj₂ (λ eq → ¬id (Equivalence.to (lemma-4-1-circuit C) eq))


------------------------------------------------------------------------
-- The end of the reduction, syntactically

-- Whatever chain ends without path variables, the circuit is the
-- identity exactly when that endpoint is syntactically |x⟩ ↦ |x⟩.

corollary-4-4-any : (C : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-any C {ξ′} steps = mk⇔
  (λ eq → Equivalence.to (Syn.id⇔syntactic ξ′)
            (Equivalence.to (reduct≋ C steps) eq))
  (λ s → Equivalence.from (reduct≋ C steps)
           (Equivalence.from (Syn.id⇔syntactic ξ′) s))

-- In particular such a chain ends at the identity's polynomials
-- exactly for the identity circuits.

corollary-4-4-syntactic : (C : Circuit n) →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntactic {n} C = mk⇔ to from
  where
  Syntactically : ∀ {k′} → PathSum n k′ 0 → Set
  Syntactically {k′} ξ′ =
    k′ ≡ 0 × (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ

  reduced : ∀ {k′} (ξ′ : PathSum n k′ 0) → ⟦ C ⟧ᴿ ⟶* ξ′ →
            Syntactically ξ′ →
            ∃ λ (ξ″ : PathSum n 0 0) →
              (⟦ C ⟧ᴿ ⟶* ξ″) ×
              (∀ w → out ξ″ w ≈[ + 2 ] μ x[ w ]) × phase ξ″ ≈[ pow M ] 0ᴾ
  reduced ξ′ steps (refl , outs , ph) = ξ′ , steps , outs , ph

  pick : ⟦ C ⟧ ≋ idPS →
         (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
            (⟦ C ⟧ᴿ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
         ⊎ ¬ (⟦ C ⟧ ≋ idPS) →
         ∃ λ (ξ″ : PathSum n 0 0) →
           (⟦ C ⟧ᴿ ⟶* ξ″) ×
           (∀ w → out ξ″ w ≈[ + 2 ] μ x[ w ]) × phase ξ″ ≈[ pow M ] 0ᴾ
  pick eq (inj₁ (_ , ξ′ , steps , C⇔ξ′)) = reduced ξ′ steps
    (Equivalence.to (Syn.id⇔syntactic ξ′) (Equivalence.to C⇔ξ′ eq))
  pick eq (inj₂ ¬id) = contradiction eq ¬id

  to = λ eq → pick eq (corollary-4-4-⟦⟧ C)

  from : (∃ λ (ξ′ : PathSum n 0 0) →
            (⟦ C ⟧ᴿ ⟶* ξ′) ×
            (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ) →
         ⟦ C ⟧ ≋ idPS
  from (ξ′ , steps , outs , ph) = circuit-id C steps outs ph


------------------------------------------------------------------------
-- A decision procedure along that route

-- Decidability as such is elementary -- the matrix has finitely many
-- entries -- and the types do not record the route.

circuit-decidable : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidable C with corollary-4-4-⟦⟧ C
... | inj₁ (_ , ξ′ , _ , C⇔ξ′) =
  map′ (Equivalence.from C⇔ξ′) (Equivalence.to C⇔ξ′) (Dcd.decide-≋-id ξ′)
... | inj₂ ¬id = no ¬id

matrix-decidable : (C : Circuit n) →
  Dec (∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z))
matrix-decidable C =
  map′ (Equivalence.to (circuit-≋-id C)) (Equivalence.from (circuit-≋-id C))
       (circuit-decidable C)
