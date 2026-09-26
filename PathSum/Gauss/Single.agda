------------------------------------------------------------------------
-- Presentations of groups
--
-- Reading a restriction reified in one elimination step
--
-- PathSum.Gauss.Corollary reifies the isometry restriction of section
-- 4.1 (Amy, QPL 2018) of a circuit C by Gaussian elimination, ⟦ C ⟧ᴿ.
-- On a closed circuit the equation ⟦ C ⟧ᴿ ≡ just (m′ , ξ) computes, but
-- the coefficients of ξ do not in practice: each step substitutes a
-- linear form for a path variable with PathSum.Polynomial.subst, one
-- coefficient of which is a double sum over all monomials.  This module
-- makes the common one-step case readable, for any state.
--
--  * The pivot, named (pivot-first).  Elimination takes whatever pivot
--    PathSum.Gauss.Forms.pivot? finds; on a closed state that is a
--    computed wire and variable, but not syntactically the literals one
--    would write, and Agda then compares the restriction it reifies
--    with one written by hand by unfolding both phases into their
--    double sums (a first attempt was killed after 900 s).  Given the
--    equation pivot? (sig st) ≡ pivot w j piv, which is cheap to check
--    by computation, pivot-first continues elimination from the named
--    pivot instead.
--  * The phase, cheaply (step-phase).  When the pivot's solution is the
--    input x_w itself -- the pivot's wire holds y_j alone, as after a
--    final Hadamard -- the step's phase is, coefficient by coefficient,
--    PathSum.Polynomial.SubstVar's substVar with y_j dropped (fast-step),
--    whose coefficients read at most three of the original phase.
--  * Irreducibility, cheaply (Obstructed-≗, step-obstructed).  The
--    certificate of PathSum.Full.Obstruction reads four coefficients at
--    every double renumbering, so it holds of a path-sum as soon as it
--    holds of one with the same phase coefficient by coefficient; hence
--    the certificate computed on fast-step proves the restriction
--    irreducible.
--
-- PathSum.Examples.ValidationIncomplete uses all three at a closed
-- miter.  Nothing here is specific to a circuit, and nothing is about
-- equivalence: only about which polynomials elimination produces.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Gauss.Single (M₀ : ℕ) where

open import Data.Bool.Base using (true)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (inside; outside; ⊥; ⁅_⁆)
open import Data.Integer.Base using (_-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Nat.Base using (_∸_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (_∷_; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; trans; cong; subst)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; ⟨_,_⟩; phase)
open import PathSum.CRK.Circuit M using (State; poly; sig)
open import PathSum.Full.Obstruction M using (Necessary; Obstructed)
open import PathSum.Gauss M₀ using (gauss; gauss-by; step; sol; restrict)
open import PathSum.Gauss.Corollary M₀ using (restriction)
open import PathSum.Gauss.Forms using (pivot; pivot?; coefʸ)
open import PathSum.Linear using (varᴸ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (Poly; x[_]; y[_]; μ)
  renaming (subst to substᴸ)
open import PathSum.Polynomial.SubstVar using (substVar; subst-var; ∖ʸ-≗)
open import PathSum.Reduction M using (½)
open import PathSum.Reorder using (frontᴾ; front; _∖ʸ_)

private
  variable
    n m k k′ : ℕ


------------------------------------------------------------------------
-- The pivot, named

-- Elimination from a state whose pivot is known is elimination from
-- that pivot.

pivot-first : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m))
              (piv : coefʸ (sig st w) j ≡ true) →
              pivot? (sig st) ≡ pivot w j piv →
              restriction {k = k} (gauss st) ≡
              restriction {k = k} (gauss-by st (pivot w j piv))
pivot-first st w j piv e = cong (λ p → restriction (gauss-by st p)) e


------------------------------------------------------------------------
-- The phase, cheaply

-- The path-sum a step leaves when its solution is x_w: y_j replaced by
-- x_w and dropped, and the identity's outputs.

fast-step : State n (suc m) → Fin n → Fin (suc m) → PathSum n k m
fast-step st w j =
  ⟨ substVar (poly st) y[ j ] x[ w ] ∖ʸ j , (λ v → μ x[ v ]) ⟩

-- Its phase is the step's, coefficient by coefficient.

step-phase : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
             sol st w j ≡ varᴸ x[ w ] →
             ∀ γ → phase (restrict {k = k} (step st w j)) γ ≡
                   phase (fast-step {k = k′} st w j) γ
step-phase st w j e γ = trans
  (cong (λ s → (substᴸ (poly st) y[ j ] (proj₁ s) (proj₂ s) ∖ʸ j) γ) e)
  (∖ʸ-≗ j (subst-var (poly st) y[ j ] x[ w ]) γ)


------------------------------------------------------------------------
-- Irreducibility, cheaply

private
  frontᴾ-≗ : (j : Fin (suc m)) {P Q : Poly n (suc m)} →
             (∀ γ → P γ ≡ Q γ) → ∀ γ → frontᴾ j P γ ≡ frontᴾ j Q γ
  frontᴾ-≗ j h (α , b ∷ s) = h (α , insertAt s j b)

  -- The four coefficients the certificate reads.

  Necessary-≗ : (i : Fin n) (χ : PathSum n k (suc (suc m)))
                (χ′ : PathSum n k′ (suc (suc m))) →
                (∀ γ → phase χ γ ≡ phase χ′ γ) →
                Necessary i χ → Necessary i χ′
  Necessary-≗ i χ χ′ h (d₀ , inj₁ dˣ) =
    subst (pow (M ∸ 2) ∣_) (h (⊥ , inside ∷ outside ∷ ⊥)) d₀ ,
    inj₁ (subst (pow (M ∸ 1) ∣_) (h (⁅ i ⁆ , inside ∷ outside ∷ ⊥)) dˣ)
  Necessary-≗ i χ χ′ h (d₀ , inj₂ (d₀₁ , d₁)) =
    subst (pow (M ∸ 2) ∣_) (h (⊥ , inside ∷ outside ∷ ⊥)) d₀ ,
    inj₂ (subst (λ c → pow M ∣ (c - ½)) (h (⊥ , inside ∷ inside ∷ ⊥)) d₀₁ ,
          subst (pow (M ∸ 2) ∣_) (h (⊥ , outside ∷ inside ∷ ⊥)) d₁)

-- The certificate holds of ξ as soon as it holds of a path-sum with the
-- same phase.

Obstructed-≗ : (i : Fin n) (ξ : PathSum n k (suc (suc m)))
               (ζ : PathSum n k′ (suc (suc m))) →
               (∀ γ → phase ξ γ ≡ phase ζ γ) →
               Obstructed i ζ → Obstructed i ξ
Obstructed-≗ i ξ ζ h obs j j′ nec =
  obs j j′ (Necessary-≗ i (front j′ (front j ξ)) (front j′ (front j ζ))
                        (frontᴾ-≗ j′ (frontᴾ-≗ j h)) nec)

-- Hence the certificate, computed on fast-step, holds of the step's
-- restriction.

step-obstructed : (i : Fin n) (st : State n (suc (suc (suc m))))
                  (w : Fin n) (j : Fin (suc (suc (suc m)))) →
                  sol st w j ≡ varᴸ x[ w ] →
                  Obstructed i (fast-step {k = k′} st w j) →
                  Obstructed i (restrict {k = k} (step st w j))
step-obstructed {k′ = k′} {k = k} i st w j e =
  Obstructed-≗ i (restrict {k = k} (step st w j))
    (fast-step {k = k′} st w j)
    (step-phase {k = k} {k′ = k′} st w j e)
