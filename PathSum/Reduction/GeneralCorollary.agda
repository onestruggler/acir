------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.4's verdicts along chains of the full calculus
-- (Amy, QPL 2018)
--
-- PathSum.Corollary carries the verdict of a reduction of a Clifford
-- circuit's restricted path-sum ⟦ C ⟧ᴿ back to the circuit, for chains
-- of PathSum.Reduction's linear rules.  Proposition 3.1 holds for all
-- of figure 2 (PathSum.Reduction.Sound), so the same verdicts hold for
-- chains of _⟶ᴳ_, which may also use [Case] and [ω]/[HH] with
-- Boolean-valued, non-linear quotients: whatever such a chain ends
-- at, ⟦ C ⟧ is the identity exactly when the end is (reduct≋ᴳ), and
-- if the end has no path variables left, exactly when it has the
-- identity's polynomials (corollary-4-4-anyᴳ).  The linear chains
-- embed (⟶*⇒⟶ᴳ*), so these are strengthenings of PathSum.Corollary's,
-- and corollary-4-4-syntacticᴳ follows from corollary-4-4-syntactic.
-- Lemma 4.2, corrected (PathSum.Interference), refutes a circuit from
-- any reduct matching it (circuit-interferenceᴳ).
--
-- What is not claimed: that the full calculus reaches a reduct with no
-- path variables beyond the Clifford case (lemma 4.3 and corollary 4.4
-- stay on the linear rules, whose order bound lemma 2.13 gives), nor
-- anything about the time it takes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Reduction.GeneralCorollary (M₀ : ℕ) where

open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using
  (PathSum; phase; out; idPS; y₀; head-part)
open import PathSum.Circuit M using (Circuit; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Corollary M₀ using
  (lemma-4-1-circuit; corollary-4-4-syntactic)
open import PathSum.Denotation M₀ using (_≋_; ≋-sym; ≋-trans)
open import PathSum.Identity M₀ using (id-if)
open import PathSum.Interference M₀ using (interferenceᴳ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; μ; x[_]; y[_]; 0ᴾ; _·ᴾ_; _≈[_]_; NoVar)
open import PathSum.Reduction M using (½; _⟶*_)
open import PathSum.Reduction.General M using (_⟶ᴳ*_; ⟶*⇒⟶ᴳ*)
open import PathSum.Reduction.Sound M₀ using (⟶ᴳ*-sound)
open import PathSum.Syntactic M₀ using (id⇔syntactic)

private
  variable
    n k′ m′ : ℕ


------------------------------------------------------------------------
-- The verdict, transported back to the circuit

-- A reduct along the full calculus is equivalent to ⟦ C ⟧ᴿ, and
-- lemma 4.1 at the circuit carries that to ⟦ C ⟧.  The reduct may
-- still have path variables.

reduct≋ᴳ : (C : Circuit n) {ξ′ : PathSum n k′ m′} → ⟦ C ⟧ᴿ ⟶ᴳ* ξ′ →
           (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
reduct≋ᴳ C {ξ′ = ξ′} steps = mk⇔
  (λ eq → ≋-trans {ξ = ξ′} {ζ = ⟦ C ⟧ᴿ} {χ = idPS}
            (≋-sym {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} (⟶ᴳ*-sound steps))
            (Equivalence.to (lemma-4-1-circuit C) eq))
  (λ eq → Equivalence.from (lemma-4-1-circuit C)
            (≋-trans {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} {χ = idPS}
                     (⟶ᴳ*-sound steps) eq))

circuit-idᴳ : (C : Circuit n) {ξ′ : PathSum n 0 0} → ⟦ C ⟧ᴿ ⟶ᴳ* ξ′ →
              (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) →
              phase ξ′ ≈[ pow M ] 0ᴾ →
              ⟦ C ⟧ ≋ idPS
circuit-idᴳ C {ξ′} steps eqf eqP =
  Equivalence.from (reduct≋ᴳ C steps) (id-if ξ′ eqf eqP)

circuit-not-idᴳ : (C : Circuit n) {ξ′ : PathSum n k′ m′} →
                  ⟦ C ⟧ᴿ ⟶ᴳ* ξ′ → ¬ (ξ′ ≋ idPS) → ¬ (⟦ C ⟧ ≋ idPS)
circuit-not-idᴳ C steps ¬id C≋id =
  ¬id (Equivalence.to (reduct≋ᴳ C steps) C≋id)


------------------------------------------------------------------------
-- The end of the reduction, syntactically

-- Whatever chain of the full calculus ends without path variables, the
-- circuit is the identity exactly when that end is syntactically
-- |x⟩ ↦ |x⟩.

corollary-4-4-anyᴳ : (C : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶ᴳ* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-anyᴳ C {ξ′} steps = mk⇔
  (λ eq → Equivalence.to (id⇔syntactic ξ′)
            (Equivalence.to (reduct≋ᴳ C steps) eq))
  (λ s → Equivalence.from (reduct≋ᴳ C steps)
           (Equivalence.from (id⇔syntactic ξ′) s))

-- Such a chain ends at the identity's polynomials exactly for the
-- identity circuits; one direction is the linear corollary, the linear
-- chains being chains of the full calculus.

corollary-4-4-syntacticᴳ : (C : Circuit n) →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C ⟧ᴿ ⟶ᴳ* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntacticᴳ {n} C = mk⇔
  (λ eq → embed (Equivalence.to (corollary-4-4-syntactic C) eq))
  (λ (ξ′ , steps , outs , ph) → circuit-idᴳ C steps outs ph)
  where
  Identity′ : PathSum n 0 0 → Set
  Identity′ ξ′ =
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ

  embed : (∃ λ (ξ′ : PathSum n 0 0) → (⟦ C ⟧ᴿ ⟶* ξ′) × Identity′ ξ′) →
          ∃ λ (ξ′ : PathSum n 0 0) → (⟦ C ⟧ᴿ ⟶ᴳ* ξ′) × Identity′ ξ′
  embed (ξ′ , steps , rest) = ξ′ , ⟶*⇒⟶ᴳ* steps , rest


------------------------------------------------------------------------
-- Lemma 4.2 at the circuit

-- A reduct matching the corrected lemma 4.2 -- the head of the phase
-- ½Q with y₀ internal, Q free of path variables modulo 2 and not ≡ 0
-- modulo 2 -- refutes the circuit.

circuit-interferenceᴳ :
  (C : Circuit n) {ξ′ : PathSum n k′ (suc m′)} → ⟦ C ⟧ᴿ ⟶ᴳ* ξ′ →
  (Q : Poly n m′) →
  head-part (phase ξ′) ≈[ pow M ] (½ ·ᴾ Q) →
  (∀ w → NoVar (+ 2) y₀ (out ξ′ w)) →
  (∀ j → NoVar (+ 2) y[ j ] Q) →
  ¬ (Q ≈[ + 2 ] 0ᴾ) →
  ¬ (⟦ C ⟧ ≋ idPS)
circuit-interferenceᴳ C {ξ′} steps Q eqP eqf noy nonzero =
  circuit-not-idᴳ C steps (interferenceᴳ ξ′ Q eqP eqf noy nonzero)
