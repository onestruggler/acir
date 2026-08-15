------------------------------------------------------------------------
-- Presentations of groups
--
-- The path-sum reduction rules (Amy, QPL 2018, figure 2)
--
-- The rules [Elim], [ω] and [HH] are formalised below.  In each of
-- them the quotient of the phase by the eliminated path variable y₀
-- is a Z₂-linear form  c ⊕ ⨁_{u ∈ S} u,  which is the shape produced
-- by a second-order phase polynomial and hence the only shape used in
-- section 4.3; a general Boolean-valued quotient would additionally
-- require products of phase polynomials.  The fourth rule of figure 2,
-- [Case], is not needed for Clifford completeness -- lemma 4.3 appeals
-- only to [Elim], [HH] and [ω] -- and its left-hand side is a pair of
-- decompositions whose right-hand side multiplies phase polynomials by
-- an input variable, so it is omitted here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Reduction (M : ℕ) where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (outside)
open import Data.Integer.Base using (ℤ; +_)
open import Data.Nat.Base using (zero; suc; _∸_)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (_∷_)

open import PathSum.Base
open import PathSum.Order M
open import PathSum.Polynomial

private
  variable
    d k n m : ℕ


------------------------------------------------------------------------
-- The dyadic constants of figure 2

⅛ ¼ ½ : ℤ
⅛ = pow (M ∸ 3)
¼ = pow (M ∸ 2)
½ = pow (M ∸ 1)


------------------------------------------------------------------------
-- The reducts

-- [Elim] and [ω] simply discard y₀; [HH] additionally substitutes the
-- linear form for the path variable y i.

elim-reduct : PathSum n (suc (suc k)) (suc m) → PathSum n k m
elim-reduct ξ = ⟨ tail-part (phase ξ) , (λ w → tail-part (out ξ w)) ⟩

ω-reduct : PathSum n (suc k) (suc m) → Bool → Mon n m → PathSum n k m
ω-reduct ξ c S =
  ⟨ (κ ⅛ -ᴾ (¼ ·ᴾ liftXor c S)) +ᴾ tail-part (phase ξ)
  , (λ w → tail-part (out ξ w)) ⟩

-- In [HH] the quotient is ½(y i + Q); with the quotient written as a
-- linear form this says that y i belongs to S, and Q is the form on
-- the remaining variables, which is what gets substituted for y i.

hh-reduct : PathSum n k (suc m) → Fin m → Bool → Mon n m → PathSum n k m
hh-reduct ξ i c S =
  ⟨ subst (tail-part (phase ξ)) y[ i ] c (S ∖ᵐ y[ i ])
  , (λ w → subst (tail-part (out ξ w)) y[ i ] c (S ∖ᵐ y[ i ])) ⟩


------------------------------------------------------------------------
-- The reduction relation

infix 4 _⟶_ _⟶*_

data _⟶_ {n : ℕ} : ∀ {k m k′ m′} →
                   PathSum n k m → PathSum n k′ m′ → Set where

  elim : ∀ {k m} (ξ : PathSum n (suc (suc k)) (suc m)) →
         head-part (phase ξ) ≈[ pow M ] 0ᴾ →
         (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
         ξ ⟶ elim-reduct ξ

  ω    : ∀ {k m} (ξ : PathSum n (suc k) (suc m)) (c : Bool) (S : Mon n m) →
         head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)) →
         (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
         ξ ⟶ ω-reduct ξ c S

  hh   : ∀ {k m} (ξ : PathSum n k (suc m)) (i : Fin m) (c : Bool)
         (S : Mon n m) → y[ i ] ∈ᵐ S →
         head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
         (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
         ξ ⟶ hh-reduct ξ i c S

-- Every rule strictly decreases the number of path variables, so the
-- relation is terminating (proposition 3.2); the closure below is
-- heterogeneous in that number.

data _⟶*_ {n : ℕ} : ∀ {k m k′ m′} →
                    PathSum n k m → PathSum n k′ m′ → Set where
  ε   : ∀ {k m} {ξ : PathSum n k m} → ξ ⟶* ξ
  _◅_ : ∀ {k m k′ m′ k″ m″} {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
        {ξ′ : PathSum n k″ m″} → ξ ⟶ ζ → ζ ⟶* ξ′ → ξ ⟶* ξ′


------------------------------------------------------------------------
-- Order of the discarded polynomials

-- Discarding y₀ cannot raise the order.

tail-Ord≤ : {P : Poly n (suc m)} → Ord≤ d P → Ord≤ d (tail-part P)
tail-Ord≤ ordP (α , β) = ordP (α , outside ∷ β)
