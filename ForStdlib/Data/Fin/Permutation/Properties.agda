------------------------------------------------------------------------
-- The Agda standard library
--
-- The group of permutations of Fin n (the symmetric group Sₙ)
--
-- The standard library defines Permutation′ n with composition _∘ₚ_,
-- identity id and inverse flip, but does not bundle them as a Group.
-- (Staged in ForStdlib for upstreaming into
-- Data.Fin.Permutation.Properties.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Data.Fin.Permutation.Properties where

open import Algebra.Bundles using (Group)
open import Algebra.Structures using (IsMonoid ; IsGroup)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Permutation
  using ( Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip ; _≈_
        ; inverseˡ ; inverseʳ )
  renaming (id to idP)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
import Function.Endo.Propositional as Endo
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; sym ; trans)
open import Relation.Binary.Structures using (IsEquivalence)

------------------------------------------------------------------------
-- The symmetric group on Fin n

-- Permutations of Fin n under composition, with the identity
-- permutation and inverse via flip.
Permutation′-group : ∀ (n : ℕ) → Group _ _
Permutation′-group n = record
  { Carrier = Permutation′ n
  ; _≈_     = _≈_
  ; _∙_     = _∘ₚ_
  ; ε       = idP
  ; _⁻¹     = flip
  ; isGroup = perm-isGroup
  }
  where
  -- Pull the endomorphism-monoid laws for Fin n → Fin n (all proved by refl).
  open IsMonoid (Endo.∘-id-isMonoid (Fin n))
    using (assoc ; identity)

  -- _≈_ is an equivalence relation (pointwise _≡_)
  ≈-isEquiv : IsEquivalence (_≈_ {m = n} {n = n})
  ≈-isEquiv = record
    { refl  = λ _   → refl
    ; sym   = λ h i → sym (h i)
    ; trans = λ p q i → trans (p i) (q i)
    }

  -- _∘ₚ_ is congruent: if π₁ ≈ π₂ and ρ₁ ≈ ρ₂ then π₁ ∘ₚ ρ₁ ≈ π₂ ∘ₚ ρ₂.
  ∘ₚ-cong : ∀ {π₁ π₂ ρ₁ ρ₂ : Permutation′ n}
           → π₁ ≈ π₂ → ρ₁ ≈ ρ₂ → π₁ ∘ₚ ρ₁ ≈ π₂ ∘ₚ ρ₂
  ∘ₚ-cong {ρ₁ = ρ₁} h₁ h₂ i = trans (cong (ρ₁ ⟨$⟩ʳ_) (h₁ i)) (h₂ _)

  -- Associativity of _∘ₚ_ is pointwise associativity of _∘_.
  ∘ₚ-assoc : ∀ (π ρ σ : Permutation′ n) → (π ∘ₚ ρ) ∘ₚ σ ≈ π ∘ₚ (ρ ∘ₚ σ)
  ∘ₚ-assoc π ρ σ i =
    cong (λ f → f i) (assoc (σ ⟨$⟩ʳ_) (ρ ⟨$⟩ʳ_) (π ⟨$⟩ʳ_))

  ∘ₚ-identityˡ : ∀ (π : Permutation′ n) → idP ∘ₚ π ≈ π
  ∘ₚ-identityˡ π i =
    cong (λ f → f i) (proj₂ identity (π ⟨$⟩ʳ_))

  ∘ₚ-identityʳ : ∀ (π : Permutation′ n) → π ∘ₚ idP ≈ π
  ∘ₚ-identityʳ π i =
    cong (λ f → f i) (proj₁ identity (π ⟨$⟩ʳ_))

  flip-invˡ : ∀ (π : Permutation′ n) → flip π ∘ₚ π ≈ idP
  flip-invˡ π _ = inverseʳ π

  flip-invʳ : ∀ (π : Permutation′ n) → π ∘ₚ flip π ≈ idP
  flip-invʳ π _ = inverseˡ π

  flip-cong : ∀ {π ρ : Permutation′ n} → π ≈ ρ → flip π ≈ flip ρ
  flip-cong {π = π} {ρ = ρ} h i =
    ρ-inj (trans (trans (sym (h (π ⟨$⟩ˡ i))) (inverseʳ π)) (sym (inverseʳ ρ)))
    where
    ρ-inj : ∀ {a b} → ρ ⟨$⟩ʳ a ≡ ρ ⟨$⟩ʳ b → a ≡ b
    ρ-inj eq =
      trans (sym (inverseˡ ρ)) (trans (cong (ρ ⟨$⟩ˡ_) eq) (inverseˡ ρ))

  perm-isGroup : IsGroup _≈_ _∘ₚ_ idP flip
  perm-isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≈-isEquiv
          ; ∙-cong        = λ {π₁} {π₂} {ρ₁} {ρ₂} h₁ h₂ → ∘ₚ-cong {π₁ = π₁} {π₂ = π₂} {ρ₁ = ρ₁} {ρ₂ = ρ₂} h₁ h₂
          }
        ; assoc = ∘ₚ-assoc
        }
      ; identity = ∘ₚ-identityˡ , ∘ₚ-identityʳ
      }
    ; inverse = flip-invˡ , flip-invʳ
    ; ⁻¹-cong = λ {π} {ρ} h → flip-cong {π = π} {ρ = ρ} h
    }
