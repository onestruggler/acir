------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.4 at a Clifford circuit, along chains of all of figure 2
--
-- PathSum.Corollary carries the verdict of a chain of head rules on
-- ⟦ C ⟧ᴿ back to the circuit, and PathSum.Anywhere.Corollary observes
-- that the argument uses nothing of the chain but its soundness
-- (reduct≋-by, syntactic-by).  With proposition 3.1 for the whole of
-- figure 2 at any variables (PathSum.Full.Sound.⟶ᶠ*-sound) the same
-- verdicts hold along chains of _⟶ᶠ_, which may use [Case], and [ω] and
-- [HH] with any Boolean-valued quotients:
--
-- * reduct≋ᶠ: whatever ⟦ C ⟧ᴿ reduces to, the circuit is the identity
--   exactly when the reduct is (lemma 4.1 at the circuit, and
--   soundness);
-- * corollary-4-4-anyᶠ: for any such chain ending without path
--   variables, the circuit is the identity exactly when the end is
--   syntactically |x⟩ ↦ |x⟩ (no normalisation, outputs the inputs mod
--   2, phase 0 mod 1), so the verdict depends neither on the order of
--   the rules nor on which rules were used; circuit-idᶠ and
--   circuit-not-idᶠ are its two halves;
-- * corollary-4-4-syntacticᶠ: the identity circuits are those for
--   which some chain ends at the identity's polynomials;
-- * circuit-normal-formᶠ: ⟦ C ⟧ᴿ reduces to a path-sum to which no
--   rule of figure 2 applies (PathSum.Full.Match), whose being the
--   identity is exactly the circuit's (normal-form-≋ᶠ for any
--   path-sum).
--
-- Everything here uses only soundness.  That an irreducible end of
-- ⟦ C ⟧ᴿ with path variables left refutes the circuit -- the paper's
-- route through lemma 4.3 -- needs every step to keep the path-sum
-- Clifford, and is PathSum.Full.Clifford (irreducible-refutesᶠ,
-- corollary-4-4-normalᶠ).  The polynomial time bounds are not
-- formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Full.Corollary (M₀ : ℕ) where

open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.Circuit M using (Circuit; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (μ; x[_]; 0ᴾ; _≈[_]_)
open import PathSum.Reduction M using (_⟶*_)
open import PathSum.Full M using (_⟶ᶠ*_; ⟶*⇒⟶ᶠ*)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Full.Match M using (Irreducibleᶠ; normal-formᶠ)

import PathSum.Denotation
private module Den = PathSum.Denotation M₀

open Den using (_≋_)

import PathSum.Identity
private module Idn = PathSum.Identity M₀

import PathSum.Corollary
private module Cor = PathSum.Corollary M₀

import PathSum.Anywhere.Corollary
private module AC = PathSum.Anywhere.Corollary M₀

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- The verdict of a reduct

-- Proposition 3.1 along the chain, and lemma 4.1 at the circuit.  The
-- reduct may still have path variables.

reduct≋ᶠ : (C : Circuit n) {ξ′ : PathSum n k′ m′} → ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ →
           (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
reduct≋ᶠ C {ξ′ = ξ′} steps = AC.reduct≋-by C {ξ′ = ξ′} (⟶ᶠ*-sound steps)

-- Without path variables left, PathSum.Identity's criterion and its
-- refutations carry back to the circuit.

circuit-idᶠ : (C : Circuit n) {ξ′ : PathSum n 0 0} → ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ →
              (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) →
              phase ξ′ ≈[ pow M ] 0ᴾ →
              ⟦ C ⟧ ≋ idPS
circuit-idᶠ C {ξ′} steps eqf eqP =
  Equivalence.from (reduct≋ᶠ C {ξ′ = ξ′} steps) (Idn.id-if ξ′ eqf eqP)

circuit-not-idᶠ : (C : Circuit n) {ξ′ : PathSum n k′ m′} →
                  ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ → ¬ (ξ′ ≋ idPS) → ¬ (⟦ C ⟧ ≋ idPS)
circuit-not-idᶠ C {ξ′} steps ¬id C≋id =
  ¬id (Equivalence.to (reduct≋ᶠ C {ξ′ = ξ′} steps) C≋id)


------------------------------------------------------------------------
-- Corollary 4.4 along any chain of figure 2

-- Whichever chain of rules of figure 2, at whichever variables, ends
-- without path variables, the circuit is the identity exactly when
-- that end is syntactically |x⟩ ↦ |x⟩.

corollary-4-4-anyᶠ : (C : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-anyᶠ C {ξ′} steps =
  AC.syntactic-by C {ξ′ = ξ′} (⟶ᶠ*-sound steps)

-- The identity circuits are those for which some such chain ends at
-- the identity's polynomials; one direction is the head-rule chain of
-- PathSum.Corollary.corollary-4-4-syntactic, read as a chain of _⟶ᶠ_.

corollary-4-4-syntacticᶠ : (C : Circuit n) →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C ⟧ᴿ ⟶ᶠ* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntacticᶠ {n} C = mk⇔ to from
  where
  to : ⟦ C ⟧ ≋ idPS →
       ∃ λ (ξ′ : PathSum n 0 0) →
         (⟦ C ⟧ᴿ ⟶ᶠ* ξ′) ×
         (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ
  to eq = lift (Equivalence.to (Cor.corollary-4-4-syntactic C) eq)
    where
    lift : (∃ λ (ξ′ : PathSum n 0 0) →
              (⟦ C ⟧ᴿ ⟶* ξ′) ×
              (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ) →
           ∃ λ (ξ′ : PathSum n 0 0) →
             (⟦ C ⟧ᴿ ⟶ᶠ* ξ′) ×
             (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ
    lift (ξ′ , steps , outs , ph) = ξ′ , ⟶*⇒⟶ᶠ* steps , outs , ph

  from : (∃ λ (ξ′ : PathSum n 0 0) →
            (⟦ C ⟧ᴿ ⟶ᶠ* ξ′) ×
            (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ) →
         ⟦ C ⟧ ≋ idPS
  from (ξ′ , steps , outs , ph) = circuit-idᶠ C steps outs ph


------------------------------------------------------------------------
-- Normal forms

-- Every path-sum reduces to an irreducible one with the same
-- denotation (proposition 3.2 with proposition 3.1) ...

normal-form-≋ᶠ : (ξ : PathSum n k m) →
                 ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
                   (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′ × ξ ≋ ξ′
normal-form-≋ᶠ {n = n} ξ = pack (normal-formᶠ ξ)
  where
  -- A helper rather than `with`: the goal mentions _≋_.
  pack : (∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
            (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′) →
         ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
           (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′ × ξ ≋ ξ′
  pack (k′ , m′ , ξ′ , steps , irr) =
    k′ , m′ , ξ′ , steps , irr , ⟶ᶠ*-sound {ξ = ξ} {ζ = ξ′} steps

-- ... and at a circuit, the irreducible end decides the circuit.

circuit-normal-formᶠ : (C : Circuit n) →
  ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
    (⟦ C ⟧ᴿ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′ × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
circuit-normal-formᶠ {n} C = pack (normal-formᶠ ⟦ C ⟧ᴿ)
  where
  pack : (∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
            (⟦ C ⟧ᴿ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′) →
         ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
           (⟦ C ⟧ᴿ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′ × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
  pack (k′ , m′ , ξ′ , steps , irr) =
    k′ , m′ , ξ′ , steps , irr , reduct≋ᶠ C {ξ′ = ξ′} steps
