------------------------------------------------------------------------
-- Presentations of groups
--
-- Verifying a circuit over {H, CNOT, R_k, R_k†} against a path-sum
-- specification (Amy, QPL 2018, sections 3 and 5.2)
--
-- Section 5.2 verifies Clifford+T implementations "directly against
-- their specification as a path sum", and section 3 says how: "check
-- that the path-sum miter ⟦C†⟧ ∘ ξ is the identity transformation",
-- by reducing it with the rules of figure 2.  PathSum.CRK.Miter.Compose
-- forms that miter by definition 2.6 and proves ⟦ C ⟧ ≋ ξ exactly when
-- it is the identity (spec-miter-∘), for any ξ.  With proposition 3.1
-- for all of figure 2 at any variables (PathSum.Full.Sound), the
-- verdict of any reduct of the miter is the verdict on C:
--
--  * spec-reduct: whatever ⟦ C† ⟧ ∘ᴾ ξ reduces to, ⟦ C ⟧ ≋ ξ exactly
--    when the reduct is the identity;
--  * spec-sound: a chain to the identity's polynomials proves
--    ⟦ C ⟧ ≋ ξ, and spec-any: any chain that ends without path
--    variables decides it syntactically (PathSum.Syntactic);
--  * spec-refuted-interference and spec-refuted-interference-at: a
--    reduct that matches lemma 4.2 (corrected, PathSum.Interference)
--    at y₀ or at any path variable refutes it;
--  * spec-normal-form: the miter reduces to a path-sum to which no
--    rule applies and whose being the identity decides the question.
--
-- As for circuits against circuits (PathSum.CRK.Validation), this is
-- sound and, beyond Clifford circuits and specifications, not
-- complete: an irreducible normal form with path variables left that
-- matches no case of lemma 4.2 gives no verdict.  Section 4.1's
-- isometry restriction is not applied here: Gaussian elimination is
-- formalised on the state a circuit runs to (PathSum.Gauss), not on a
-- composite of path-sums, so the whole miter is reduced.  For a
-- WellFormed ξ the diagonal of the miter would decide the question
-- (PathSum.CRK.Miter.Compose's spec-miter-restriction).
--
-- These are theorems for symbolic use.  On a closed instance the
-- miter's polynomials do not compute -- a composite is built by
-- substitution, which is opaque (PathSum.Polynomial.Bind) -- so,
-- unlike the circuit miters of PathSum.Examples.Validation, their
-- premises cannot be discharged by computing decisions.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.Specification (M₀ : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (trans to ⇔-trans)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; phase; out; idPS; y₀; head-part)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.CRK.Adjoint M using (_†)
open import PathSum.CRK.Circuit M using (Circuit; ⟦_⟧)
open import PathSum.CRK.Miter.Compose M₀ using (spec-miter-∘)
open import PathSum.CRK.Validation M₀ using (interference-at-var)
open import PathSum.Denotation M₀ using (_≋_; ≋-sym; ≋-trans)
open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Match M using (Irreducibleᶠ; normal-formᶠ)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Identity M₀ using (id-if)
open import PathSum.Interference M₀ using (interferenceᴳ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; μ; x[_]; y[_]; 0ᴾ; _·ᴾ_; _≈[_]_; NoVar)
open import PathSum.Reduction M using (½)
open import PathSum.Reorder using (_/ʸ_)
open import PathSum.Syntactic M₀ using (id⇔syntactic)

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- The verdict of a reduct of the miter

-- Proposition 3.1 along the chain, then spec-miter-∘.

spec-reduct : (C : Circuit n) (ξ : PathSum n k m)
              {ξ′ : PathSum n k′ m′} → (⟦ C † ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ′ →
              (⟦ C ⟧ ≋ ξ ⇔ ξ′ ≋ idPS)
spec-reduct C ξ {ξ′} steps = ⇔-trans (spec-miter-∘ C ξ) (mk⇔
  (λ e → ≋-trans {ξ = ξ′} {ζ = ⟦ C † ⟧ ∘ᴾ ξ} {χ = idPS}
           (≋-sym {ξ = ⟦ C † ⟧ ∘ᴾ ξ} {ζ = ξ′} sound) e)
  (λ e → ≋-trans {ξ = ⟦ C † ⟧ ∘ᴾ ξ} {ζ = ξ′} {χ = idPS} sound e))
  where
  sound : (⟦ C † ⟧ ∘ᴾ ξ) ≋ ξ′
  sound = ⟶ᶠ*-sound {ξ = ⟦ C † ⟧ ∘ᴾ ξ} {ζ = ξ′} steps


------------------------------------------------------------------------
-- Soundness, and the end of a chain

-- A chain to the identity's polynomials proves ⟦ C ⟧ ≋ ξ ...

spec-sound : (C : Circuit n) (ξ : PathSum n k m)
             {ξ′ : PathSum n 0 0} → (⟦ C † ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ′ →
             (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) →
             phase ξ′ ≈[ pow M ] 0ᴾ →
             ⟦ C ⟧ ≋ ξ
spec-sound C ξ {ξ′} steps outs ph =
  Equivalence.from (spec-reduct C ξ {ξ′ = ξ′} steps) (id-if ξ′ outs ph)

-- ... and any chain that ends without path variables decides it
-- syntactically.

spec-any : (C : Circuit n) (ξ : PathSum n k m)
           {ξ′ : PathSum n k′ 0} → (⟦ C † ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ′ →
           (⟦ C ⟧ ≋ ξ ⇔
            (k′ ≡ 0 ×
             (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
spec-any C ξ {ξ′} steps =
  ⇔-trans (spec-reduct C ξ {ξ′ = ξ′} steps) (id⇔syntactic ξ′)


------------------------------------------------------------------------
-- Lemma 4.2 refutes

-- At y₀ ...

spec-refuted-interference : (C : Circuit n) (ξ : PathSum n k m)
  {ξ″ : PathSum n k″ (suc m″)} → (⟦ C † ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ″ →
  (Q : Poly n m″) →
  head-part (phase ξ″) ≈[ pow M ] (½ ·ᴾ Q) →
  (∀ w → NoVar (+ 2) y₀ (out ξ″ w)) →
  (∀ j → NoVar (+ 2) y[ j ] Q) →
  ¬ (Q ≈[ + 2 ] 0ᴾ) →
  ¬ (⟦ C ⟧ ≋ ξ)
spec-refuted-interference C ξ {ξ″} steps Q eqP eqf noy nonzero e =
  interferenceᴳ ξ″ Q eqP eqf noy nonzero
    (Equivalence.to (spec-reduct C ξ {ξ′ = ξ″} steps) e)

-- ... and at any path variable y_j.

spec-refuted-interference-at : (C : Circuit n) (ξ : PathSum n k m)
  {ξ″ : PathSum n k″ (suc m″)} → (⟦ C † ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ″ →
  (j : Fin (suc m″)) (Q : Poly n m″) →
  (phase ξ″ /ʸ j) ≈[ pow M ] (½ ·ᴾ Q) →
  (∀ w → NoVar (+ 2) y[ j ] (out ξ″ w)) →
  (∀ i → NoVar (+ 2) y[ i ] Q) →
  ¬ (Q ≈[ + 2 ] 0ᴾ) →
  ¬ (⟦ C ⟧ ≋ ξ)
spec-refuted-interference-at C ξ {ξ″} steps j Q eqP eqf noy nonzero e =
  interference-at-var ξ″ j Q eqP eqf noy nonzero
    (Equivalence.to (spec-reduct C ξ {ξ′ = ξ″} steps) e)


------------------------------------------------------------------------
-- Normal forms

-- The miter reduces to an irreducible path-sum whose being the
-- identity decides ⟦ C ⟧ ≋ ξ.

spec-normal-form : (C : Circuit n) (ξ : PathSum n k m) →
  ∃ λ k″ → ∃ λ m″ → ∃ λ (ξ′ : PathSum n k″ m″) →
    ((⟦ C † ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′ × (⟦ C ⟧ ≋ ξ ⇔ ξ′ ≋ idPS)
spec-normal-form {n = n} C ξ = pack (normal-formᶠ (⟦ C † ⟧ ∘ᴾ ξ))
  where
  pack : (∃ λ k″ → ∃ λ m″ → ∃ λ (ξ′ : PathSum n k″ m″) →
            ((⟦ C † ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′) →
         ∃ λ k″ → ∃ λ m″ → ∃ λ (ξ′ : PathSum n k″ m″) →
           ((⟦ C † ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′ ×
           (⟦ C ⟧ ≋ ξ ⇔ ξ′ ≋ idPS)
  pack (k″ , m″ , ξ′ , steps , irr) =
    k″ , m″ , ξ′ , steps , irr , spec-reduct C ξ {ξ′ = ξ′} steps
