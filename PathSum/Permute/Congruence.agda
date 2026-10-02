------------------------------------------------------------------------
-- Presentations of groups
--
-- Congruence up to renaming is an equivalence (Amy, QPL 2018, remark
-- 2.8)
--
-- PathSum.Permute.Sound defines ξ ≈ᴿ⟨ π ⟩ ζ: the same normalisation,
-- and ξ with its path variables renamed by π congruent to ζ -- phases
-- modulo 2^M and outputs modulo 2, coefficient by coefficient.  It is
-- the form in which some laws of remark 2.8 hold (those where
-- definition 2.6 substitutes lifted outputs, which agree with the
-- outputs they lift only modulo 2), and it was stated there without
-- its algebra.  Here it is: ≈ᴿ is reflexive along the identity
-- renaming (≈ᴿ-refl), symmetric along the inverse renaming (≈ᴿ-sym),
-- transitive along the composite renaming (≈ᴿ-trans), depends on the
-- renaming only through its values (≈ᴿ-cong), and absorbs equality up
-- to renaming on either side (≡ᴿ-≈ᴿ, ≈ᴿ-≡ᴿ).  So laws proved as ≡ᴿ and
-- as ≈ᴿ chain into ≈ᴿ, which PathSum.Permute.Sound.≈ᴿ⇒≋ turns into ≋.
--
-- The proofs are coefficient by coefficient: renaming along π and then
-- ρ is renaming along the composite (PathSum.Permute.renumberᴾ-∘), a
-- renaming acts on each coefficient by re-indexing it, and the
-- congruences modulo c compose (PathSum.Polynomial.Product's ≈-sym,
-- ≈-trans).  Nothing is evaluated.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Permute.Congruence (M₀ : ℕ) where

open import Data.Fin.Permutation using
  (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_; inverseˡ; id; flip; _∘ₚ_)
open import Data.Fin.Subset using (Subset)
open import Data.Integer.Base using (ℤ; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Permute using
  (pullˢ; pullˢ-id; pullˢ-∘; pullˢ-cong; renumberᴾ; renumberᴾ-∘;
   renumberᴾ-cong; _≡ᴿ⟨_⟩_; ≡ᴿ-refl)
open import PathSum.Permute.Sound M₀ using
  (_≈ᴿ⟨_⟩_; congruent-renamed; ≡ᴿ⇒≈ᴿ)
open import PathSum.Polynomial using (Poly; _≈[_]_)
open import PathSum.Polynomial.Product using (≈-sym; ≈-trans)

private
  variable
    n k k′ k″ m m′ m″ : ℕ


------------------------------------------------------------------------
-- Renaming respects congruence

-- A renaming re-indexes the coefficients, so congruent polynomials
-- stay congruent.

renumber-≈ : ∀ {c} (π : Permutation m m′) {P Q : Poly n m} →
             P ≈[ c ] Q → renumberᴾ π P ≈[ c ] renumberᴾ π Q
renumber-≈ π h (α , β) = h (α , pullˢ (π ⟨$⟩ʳ_) β)

-- Pointwise equal polynomials are interchangeable on the left of a
-- congruence.

private
  ≈-≡ˡ : ∀ {c} {P P′ Q : Poly n m} → (∀ γ → P γ ≡ P′ γ) →
         P ≈[ c ] Q → P′ ≈[ c ] Q
  ≈-≡ˡ {c = c} {Q = Q} e h γ = subst (λ v → c ∣ (v - Q γ)) (e γ) (h γ)

  -- Renaming along π, then back along its inverse, changes nothing.
  pull-back : (π : Permutation m m′) (β : Subset m) →
              pullˢ (π ⟨$⟩ʳ_) (pullˢ (π ⟨$⟩ˡ_) β) ≡ β
  pull-back π β = trans (pullˢ-∘ (π ⟨$⟩ʳ_) (π ⟨$⟩ˡ_) β)
    (trans (pullˢ-cong (λ i → inverseˡ π) β) (pullˢ-id β))

  -- The coefficient-wise step of each law.
  sym-step : ∀ {c} (π : Permutation m m′) (P : Poly n m) (Q : Poly n m′) →
             renumberᴾ π P ≈[ c ] Q → renumberᴾ (flip π) Q ≈[ c ] P
  sym-step {c = c} π P Q h (α , β) =
    subst (λ v → c ∣ (Q (α , pullˢ (π ⟨$⟩ˡ_) β) - v))
          (cong (λ b → P (α , b)) (pull-back π β))
          (≈-sym {P = renumberᴾ π P} {Q = Q} h (α , pullˢ (π ⟨$⟩ˡ_) β))

  trans-step : ∀ {c} (π : Permutation m m′) (ρ : Permutation m′ m″)
               (P : Poly n m) (Q : Poly n m′) (R : Poly n m″) →
               renumberᴾ π P ≈[ c ] Q → renumberᴾ ρ Q ≈[ c ] R →
               renumberᴾ (π ∘ₚ ρ) P ≈[ c ] R
  trans-step π ρ P Q R h₁ h₂ = ≈-≡ˡ (renumberᴾ-∘ π ρ P)
    (≈-trans {P = renumberᴾ ρ (renumberᴾ π P)} {Q = renumberᴾ ρ Q} {R = R}
             (renumber-≈ ρ {P = renumberᴾ π P} {Q = Q} h₁) h₂)


------------------------------------------------------------------------
-- An equivalence

-- The identity renaming, the inverse, the composite.

≈ᴿ-refl : (ξ : PathSum n k m) → ξ ≈ᴿ⟨ id ⟩ ξ
≈ᴿ-refl ξ = ≡ᴿ⇒≈ᴿ {ξ = ξ} {π = id} {ζ = ξ} (≡ᴿ-refl ξ)

≈ᴿ-sym : {ξ : PathSum n k m} {π : Permutation m m′} {ζ : PathSum n k′ m′} →
         ξ ≈ᴿ⟨ π ⟩ ζ → ζ ≈ᴿ⟨ flip π ⟩ ξ
≈ᴿ-sym {ξ = ξ} {π} {ζ} (congruent-renamed e (ou , ph)) =
  congruent-renamed (sym e)
    ( (λ w → sym-step π (out ξ w) (out ζ w) (ou w))
    , sym-step π (phase ξ) (phase ζ) ph )

≈ᴿ-trans : {ξ : PathSum n k m} {π : Permutation m m′} {ζ : PathSum n k′ m′}
           {ρ : Permutation m′ m″} {χ : PathSum n k″ m″} →
           ξ ≈ᴿ⟨ π ⟩ ζ → ζ ≈ᴿ⟨ ρ ⟩ χ → ξ ≈ᴿ⟨ π ∘ₚ ρ ⟩ χ
≈ᴿ-trans {ξ = ξ} {π} {ζ} {ρ} {χ}
         (congruent-renamed e₁ (ou₁ , ph₁)) (congruent-renamed e₂ (ou₂ , ph₂)) =
  congruent-renamed (trans e₁ e₂)
    ( (λ w → trans-step π ρ (out ξ w) (out ζ w) (out χ w) (ou₁ w) (ou₂ w))
    , trans-step π ρ (phase ξ) (phase ζ) (phase χ) ph₁ ph₂ )

-- Pointwise equal renamings rename alike.

≈ᴿ-cong : {ξ : PathSum n k m} {π ρ : Permutation m m′}
          {ζ : PathSum n k′ m′} →
          (∀ j → π ⟨$⟩ʳ j ≡ ρ ⟨$⟩ʳ j) → ξ ≈ᴿ⟨ π ⟩ ζ → ξ ≈ᴿ⟨ ρ ⟩ ζ
≈ᴿ-cong {ξ = ξ} {π} {ρ} π≗ρ (congruent-renamed e (ou , ph)) =
  congruent-renamed e
    ( (λ w → ≈-≡ˡ (renumberᴾ-cong {π = π} {ρ} π≗ρ (out ξ w)) (ou w))
    , ≈-≡ˡ (renumberᴾ-cong {π = π} {ρ} π≗ρ (phase ξ)) ph )

-- Equality up to renaming, on either side.

≡ᴿ-≈ᴿ : {ξ : PathSum n k m} {π : Permutation m m′} {ζ : PathSum n k′ m′}
        {ρ : Permutation m′ m″} {χ : PathSum n k″ m″} →
        ξ ≡ᴿ⟨ π ⟩ ζ → ζ ≈ᴿ⟨ ρ ⟩ χ → ξ ≈ᴿ⟨ π ∘ₚ ρ ⟩ χ
≡ᴿ-≈ᴿ {ξ = ξ} {π} {ζ} {ρ} {χ} r s =
  ≈ᴿ-trans {ξ = ξ} {π} {ζ} {ρ} {χ} (≡ᴿ⇒≈ᴿ {ξ = ξ} {π} {ζ} r) s

≈ᴿ-≡ᴿ : {ξ : PathSum n k m} {π : Permutation m m′} {ζ : PathSum n k′ m′}
        {ρ : Permutation m′ m″} {χ : PathSum n k″ m″} →
        ξ ≈ᴿ⟨ π ⟩ ζ → ζ ≡ᴿ⟨ ρ ⟩ χ → ξ ≈ᴿ⟨ π ∘ₚ ρ ⟩ χ
≈ᴿ-≡ᴿ {ξ = ξ} {π} {ζ} {ρ} {χ} s r =
  ≈ᴿ-trans {ξ = ξ} {π} {ζ} {ρ} {χ} s (≡ᴿ⇒≈ᴿ {ξ = ζ} {ρ} {χ} r)
