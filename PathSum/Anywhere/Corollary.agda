------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.4 at a Clifford circuit, in any elimination order
--
-- PathSum.Corollary carries the verdict of a chain of head rules on
-- ⟦ C ⟧ᴿ back to the circuit.  The only fact about the chain that it
-- uses is ⟦ C ⟧ᴿ ≋ ξ′ (proposition 3.1), so the argument holds for any
-- sound calculus.  reduct≋-by states it for any ξ′ equivalent to
-- ⟦ C ⟧ᴿ, and syntactic-by adds the syntactic test when ξ′ has no path
-- variables.
--
-- For the rules at any path variable (PathSum.Anywhere) this gives
-- corollary-4-4-anyᵍ: for every chain of general rules from ⟦ C ⟧ᴿ
-- that ends without path variables, the circuit is the identity
-- exactly when the end is syntactically |x⟩ ↦ |x⟩.  So the verdict
-- does not depend on which variables were eliminated, or in what
-- order.  corollary-4-4-syntacticᵍ is the matching characterisation
-- by existence of a chain.  corollary-4-4-circuit-by runs a given
-- elimination strategy on ⟦ C ⟧ᴿ (PathSum.Anywhere.Clifford): either
-- it refutes the circuit, or it reaches such an end along that
-- strategy.  As in PathSum.Corollary, the polynomial time bound is
-- not formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Anywhere.Corollary (M₀ : ℕ) where

open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Circuit M using (Circuit; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (μ; x[_]; 0ᴾ; _≈[_]_)
open import PathSum.Reduction M using (_⟶*_)
open import PathSum.Anywhere M using (_⟶ᵍ*_; ⟶*⇒⟶ᵍ*)

import PathSum.Circuit
module Circ = PathSum.Circuit M

import PathSum.Denotation
module Den = PathSum.Denotation M₀

open Den using (_≋_)

import PathSum.Syntactic
module Syn = PathSum.Syntactic M₀

import PathSum.Corollary
module Cor = PathSum.Corollary M₀

import PathSum.Anywhere.Sound
module Snd = PathSum.Anywhere.Sound M₀

import PathSum.Anywhere.Clifford
module AC = PathSum.Anywhere.Clifford M₀

private
  variable
    n k′ m′ : ℕ


------------------------------------------------------------------------
-- The verdict, for any path-sum equivalent to ⟦ C ⟧ᴿ

-- Lemma 4.1 at the circuit, composed with the equivalence.  This is
-- PathSum.Corollary.reduct≋ with the chain replaced by what it is
-- used for.

reduct≋-by : (C : Circuit n) {ξ′ : PathSum n k′ m′} → ⟦ C ⟧ᴿ ≋ ξ′ →
             (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
reduct≋-by C {ξ′ = ξ′} eqR = mk⇔
  (λ eq → Den.≋-trans {ξ = ξ′} {ζ = ⟦ C ⟧ᴿ} {χ = idPS}
            (Den.≋-sym {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} eqR)
            (Equivalence.to (Cor.lemma-4-1-circuit C) eq))
  (λ eq → Equivalence.from (Cor.lemma-4-1-circuit C)
            (Den.≋-trans {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} {χ = idPS} eqR eq))

-- Without path variables left, being the identity is syntactic
-- (PathSum.Syntactic).

syntactic-by : (C : Circuit n) {ξ′ : PathSum n k′ 0} → ⟦ C ⟧ᴿ ≋ ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
syntactic-by C {ξ′} eqR = mk⇔
  (λ eq → Equivalence.to (Syn.id⇔syntactic ξ′)
            (Equivalence.to (reduct≋-by C {ξ′ = ξ′} eqR) eq))
  (λ s → Equivalence.from (reduct≋-by C {ξ′ = ξ′} eqR)
           (Equivalence.from (Syn.id⇔syntactic ξ′) s))


------------------------------------------------------------------------
-- Corollary 4.4 for the rules at any path variable

-- Whichever chain of general rules ends without path variables, the
-- circuit is the identity exactly when that end is syntactically
-- |x⟩ ↦ |x⟩.

corollary-4-4-anyᵍ : (C : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶ᵍ* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-anyᵍ C {ξ′} steps =
  syntactic-by C {ξ′ = ξ′} (Snd.⟶ᵍ*-sound steps)

-- The identity circuits are those for which some such chain ends at
-- the identity's polynomials.  One direction is the head-rule chain of
-- PathSum.Corollary.corollary-4-4-syntactic, read as a general chain.

corollary-4-4-syntacticᵍ : (C : Circuit n) →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C ⟧ᴿ ⟶ᵍ* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntacticᵍ {n} C = mk⇔ to from
  where
  lift : (∃ λ (ξ′ : PathSum n 0 0) →
            (⟦ C ⟧ᴿ ⟶* ξ′) ×
            (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ) →
         ∃ λ (ξ′ : PathSum n 0 0) →
           (⟦ C ⟧ᴿ ⟶ᵍ* ξ′) ×
           (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ
  lift (ξ′ , steps , outs , ph) = ξ′ , ⟶*⇒⟶ᵍ* steps , outs , ph

  to = λ eq → lift (Equivalence.to (Cor.corollary-4-4-syntactic C) eq)

  from : (∃ λ (ξ′ : PathSum n 0 0) →
            (⟦ C ⟧ᴿ ⟶ᵍ* ξ′) ×
            (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ) →
         ⟦ C ⟧ ≋ idPS
  from (ξ′ , steps , outs , ph) =
    Equivalence.from (corollary-4-4-anyᵍ C steps) (refl , outs , ph)


------------------------------------------------------------------------
-- Corollary 4.4 along a strategy

-- Run the strategy on ⟦ C ⟧ᴿ: either it refutes the circuit, or its
-- chain ends without path variables, at a path-sum whose syntax
-- decides the circuit.

corollary-4-4-circuit-by : (choose : AC.Strategy n) (C : Circuit n) →
  (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
     AC.Follows choose ⟦ C ⟧ᴿ ξ′ ×
     (⟦ C ⟧ ≋ idPS ⇔
      (k′ ≡ 0 ×
       (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)))
  ⊎ ¬ (⟦ C ⟧ ≋ idPS)
corollary-4-4-circuit-by choose C =
  case AC.corollary-4-4-by choose ⟦ C ⟧ᴿ
         (Circ.⟦⟧ᴿ-Internal C) (Circ.⟦⟧ᴿ-Ord≤ C) of λ where
    (AC.done f)    →
      inj₁ (_ , _ , f , corollary-4-4-anyᵍ C (AC.Follows⇒⟶ᵍ* f))
    (AC.no-id ¬id) →
      inj₂ (λ eq → ¬id (Equivalence.to (Cor.lemma-4-1-circuit C) eq))
