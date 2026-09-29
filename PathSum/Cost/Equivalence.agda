------------------------------------------------------------------------
-- Presentations of groups
--
-- The sparse rules step the path-sums they represent, up to ≋ (for
-- Amy, QPL 2018, figure 2 and proposition 3.1)
--
-- PathSum.Cost.Rules proves each sparse rule sound syntactically: the
-- dense path-sum ξ that the input R represents steps by the rule at
-- y_j, and the output R′ represents the reduct.  "Represents" (the
-- phases agree modulo 2^M, the outputs are the liftings of the forms)
-- implies ≋ (PathSum.Size.Equivalence.represents-≋), so the reduct
-- denotes the operator of psʳ k′ R′, the path-sum R′ stands for, and --
-- by proposition 3.1 along the step (PathSum.Anywhere.Sound.⟶ᵍ-sound)
-- -- so does ξ, and so does psʳ k R.  So a rewrite on the sparse
-- representation is a rewrite of the dense path-sum it stands for,
-- and it preserves the operator.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Equivalence (M₀ : ℕ) where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (suc; _≤_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import PathSum.Anywhere.Sound M₀ using (⟶ᵍ-sound)
open import PathSum.Base using (PathSum)
open import PathSum.Cost using (value)
open import PathSum.Denotation M₀ using (_≋_; ≋-sym; ≋-trans)
open import PathSum.Polynomial using (Mon)
open import PathSum.Reorder using (front)
open import PathSum.Size.Equivalence M₀ using (represents-≋)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (_⟶ᵍ_)
open import PathSum.Cost.Canon M using (Ordᵀ)
open import PathSum.Cost.Rules M using
  (elimˢ; ωˢ; hhˢ; elimˢ-sound; ωˢ-sound; hhˢ-sound)
open import PathSum.Reduction M using (elim-reduct; ω-reduct; hh-reduct)
open import PathSum.Size.Sparse M using (Rep; terms; Represents; psʳ)

private
  variable
    k n m : ℕ

-- The step, the reduct's operator, and the operators at both ends.

elimˢ-≋ : (d : ℕ) (j : Fin (suc m)) (ξ : PathSum n (suc (suc k)) (suc m))
          (R : Rep n (suc m)) → Represents ξ R → Ordᵀ d (terms R) →
          ∀ {R′} → value (elimˢ d j R) ≡ just R′ →
          (ξ ⟶ᵍ elim-reduct (front j ξ)) ×
          (elim-reduct (front j ξ) ≋ psʳ k R′) ×
          (psʳ (suc (suc k)) R ≋ psʳ k R′)
elimˢ-≋ {k = k} d j ξ R rp ord {R′} eq =
  step , red≋ ,
  ≋-trans {ξ = psʳ (suc (suc k)) R} {ζ = ξ} {χ = psʳ k R′}
    (≋-sym {ξ = ξ} {ζ = psʳ (suc (suc k)) R} (represents-≋ ξ R rp))
    (≋-trans {ξ = ξ} {ζ = elim-reduct (front j ξ)} {χ = psʳ k R′}
             (⟶ᵍ-sound step) red≋)
  where
  sound = elimˢ-sound d j ξ R rp ord eq
  step  = proj₁ sound
  red≋  = represents-≋ (elim-reduct (front j ξ)) R′ (proj₁ (proj₂ sound))

ωˢ-≋ : (d : ℕ) → 2 ≤ d → (j : Fin (suc m)) (ξ : PathSum n (suc k) (suc m))
       (R : Rep n (suc m)) → Represents ξ R → Ordᵀ d (terms R) →
       ∀ {c S R′} → value (ωˢ d j R) ≡ just (c , S , R′) →
       (ξ ⟶ᵍ ω-reduct (front j ξ) c S) ×
       (ω-reduct (front j ξ) c S ≋ psʳ k R′) ×
       (psʳ (suc k) R ≋ psʳ k R′)
ωˢ-≋ {k = k} d 2≤d j ξ R rp ord {c} {S} {R′} eq =
  step , red≋ ,
  ≋-trans {ξ = psʳ (suc k) R} {ζ = ξ} {χ = psʳ k R′}
    (≋-sym {ξ = ξ} {ζ = psʳ (suc k) R} (represents-≋ ξ R rp))
    (≋-trans {ξ = ξ} {ζ = ω-reduct (front j ξ) c S} {χ = psʳ k R′}
             (⟶ᵍ-sound step) red≋)
  where
  sound = ωˢ-sound d 2≤d j ξ R rp ord eq
  step  = proj₁ sound
  red≋  = represents-≋ (ω-reduct (front j ξ) c S) R′ (proj₁ (proj₂ sound))

hhˢ-≋ : (d : ℕ) (j : Fin (suc m)) (ξ : PathSum n k (suc m))
        (R : Rep n (suc m)) → Represents ξ R → Ordᵀ d (terms R) →
        ∀ {i c S R′} → value (hhˢ d j R) ≡ just (i , c , S , R′) →
        (ξ ⟶ᵍ hh-reduct (front j ξ) i c S) ×
        (hh-reduct (front j ξ) i c S ≋ psʳ k R′) ×
        (psʳ k R ≋ psʳ k R′)
hhˢ-≋ {k = k} d j ξ R rp ord {i} {c} {S} {R′} eq =
  step , red≋ ,
  ≋-trans {ξ = psʳ k R} {ζ = ξ} {χ = psʳ k R′}
    (≋-sym {ξ = ξ} {ζ = psʳ k R} (represents-≋ ξ R rp))
    (≋-trans {ξ = ξ} {ζ = hh-reduct (front j ξ) i c S} {χ = psʳ k R′}
             (⟶ᵍ-sound step) red≋)
  where
  sound = hhˢ-sound d j ξ R rp ord eq
  step  = proj₁ sound
  red≋  = represents-≋ (hh-reduct (front j ξ) i c S) R′
                       (proj₁ (proj₂ sound))
