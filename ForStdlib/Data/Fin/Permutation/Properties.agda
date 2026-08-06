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
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Permutation
  using ( Permutation′ ; id ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip ; _≈_
        ; inverseˡ ; inverseʳ
        ; lift₀ ; lift₀-id ; lift₀-comp ; lift₀-cong )
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (ℕ)
open import ForStdlib.Algebra.IndexedGroups using (IndexedGroup ; Embedding)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
import Function.Endo.Propositional as Endo
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; sym ; trans)
open import Relation.Binary.Structures using (IsEquivalence)

------------------------------------------------------------------------
-- The symmetric group Sₙ, as the group of permutations of Fin n under
-- composition, with identity id and inverse flip.

∘ₚ-id-isGroup : ∀ (n : ℕ) → IsGroup (_≈_ {m = n} {n = n}) _∘ₚ_ id flip
∘ₚ-id-isGroup n = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ≈-isEquivalence
        ; ∙-cong        = λ {π₁} {π₂} {ρ₁} {ρ₂} → ∘ₚ-cong {π₁} {π₂} {ρ₁} {ρ₂}
        }
      ; assoc = ∘ₚ-assoc
      }
    ; identity = ∘ₚ-identityˡ , ∘ₚ-identityʳ
    }
  ; inverse = flip-inverseˡ , flip-inverseʳ
  ; ⁻¹-cong = λ {π} {ρ} → flip-cong {π} {ρ}
  }
  where
  -- The endomorphism-monoid laws for Fin n → Fin n (all by refl).
  open IsMonoid (Endo.∘-id-isMonoid (Fin n)) using (assoc ; identity)

  ≈-isEquivalence : IsEquivalence (_≈_ {m = n} {n = n})
  ≈-isEquivalence = record
    { refl  = λ _     → refl
    ; sym   = λ h i   → sym (h i)
    ; trans = λ p q i → trans (p i) (q i)
    }

  ∘ₚ-cong : ∀ {π₁ π₂ ρ₁ ρ₂ : Permutation′ n}
          → π₁ ≈ π₂ → ρ₁ ≈ ρ₂ → π₁ ∘ₚ ρ₁ ≈ π₂ ∘ₚ ρ₂
  ∘ₚ-cong {ρ₁ = ρ₁} h₁ h₂ i = trans (cong (ρ₁ ⟨$⟩ʳ_) (h₁ i)) (h₂ _)

  ∘ₚ-assoc : ∀ (π ρ σ : Permutation′ n) → (π ∘ₚ ρ) ∘ₚ σ ≈ π ∘ₚ (ρ ∘ₚ σ)
  ∘ₚ-assoc π ρ σ i = cong (λ f → f i) (assoc (σ ⟨$⟩ʳ_) (ρ ⟨$⟩ʳ_) (π ⟨$⟩ʳ_))

  ∘ₚ-identityˡ : ∀ (π : Permutation′ n) → id ∘ₚ π ≈ π
  ∘ₚ-identityˡ π i = cong (λ f → f i) (proj₂ identity (π ⟨$⟩ʳ_))

  ∘ₚ-identityʳ : ∀ (π : Permutation′ n) → π ∘ₚ id ≈ π
  ∘ₚ-identityʳ π i = cong (λ f → f i) (proj₁ identity (π ⟨$⟩ʳ_))

  flip-inverseˡ : ∀ (π : Permutation′ n) → flip π ∘ₚ π ≈ id
  flip-inverseˡ π _ = inverseʳ π

  flip-inverseʳ : ∀ (π : Permutation′ n) → π ∘ₚ flip π ≈ id
  flip-inverseʳ π _ = inverseˡ π

  flip-cong : ∀ {π ρ : Permutation′ n} → π ≈ ρ → flip π ≈ flip ρ
  flip-cong {π = π} {ρ = ρ} h i =
    ρ-inj (trans (trans (sym (h (π ⟨$⟩ˡ i))) (inverseʳ π)) (sym (inverseʳ ρ)))
    where
    ρ-inj : ∀ {a b} → ρ ⟨$⟩ʳ a ≡ ρ ⟨$⟩ʳ b → a ≡ b
    ρ-inj eq = trans (sym (inverseˡ ρ)) (trans (cong (ρ ⟨$⟩ˡ_) eq) (inverseˡ ρ))

∘ₚ-id-group : ∀ (n : ℕ) → Group _ _
∘ₚ-id-group n = record
  { Carrier = Permutation′ n
  ; _≈_     = _≈_
  ; _∙_     = _∘ₚ_
  ; ε       = id
  ; _⁻¹     = flip
  ; isGroup = ∘ₚ-id-isGroup n
  }

------------------------------------------------------------------------
-- Sₙ as an indexed group

-- The symmetric groups form a family indexed by the number of points.

∘ₚ-id-indexedGroup : IndexedGroup _ _
∘ₚ-id-indexedGroup = record { group = ∘ₚ-id-group }

------------------------------------------------------------------------
-- The embedding of Sₙ into Sₙ₊₁

-- lift₀ adjoins a new point 0 and fixes it, sending suc i to
-- suc (π i).  It is a group homomorphism: the standard library
-- supplies the unit and product laws (lift₀-id, lift₀-comp) and the
-- congruence (lift₀-cong), and the inverse law holds on the nose,
-- since flip only exchanges the two directions of the underlying
-- inverse pair.

lift₀-flip : ∀ {n} (π : Permutation′ n) → lift₀ (flip π) ≈ flip (lift₀ π)
lift₀-flip π zero    = refl
lift₀-flip π (suc i) = refl

-- lift₀ is injective: lift₀ π and lift₀ ρ agree at suc i exactly when
-- π and ρ agree at i, so agreement everywhere on Fin (suc n) forces
-- agreement everywhere on Fin n.  (The two permutations' behaviour at
-- 0 carries no information: both fix it.)

lift₀-injective : ∀ {n} {π ρ : Permutation′ n} → lift₀ π ≈ lift₀ ρ → π ≈ ρ
lift₀-injective π≈ρ i = suc-injective (π≈ρ (suc i))

∘ₚ-id-embedding : Embedding ∘ₚ-id-indexedGroup
∘ₚ-id-embedding = record
  { emb                 = lift₀
  ; isGroupMonomorphism = λ n → record
    { isGroupHomomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = λ {π} {ρ} → lift₀-cong π ρ }
          ; homo              = λ π ρ i → sym (lift₀-comp π ρ i)
          }
        ; ε-homo = lift₀-id
        }
      ; ⁻¹-homo = lift₀-flip
      }
    ; injective = λ {π} {ρ} → lift₀-injective {n} {π} {ρ}
    }
  }

-- Hence the k-fold embedding of Sₙ into Sₖ₊ₙ is injective too.

lift₀^-injective : ∀ {n} (k : ℕ) {π ρ : Permutation′ n} →
                   Embedding.emb^ ∘ₚ-id-embedding k π ≈
                   Embedding.emb^ ∘ₚ-id-embedding k ρ →
                   π ≈ ρ
lift₀^-injective = Embedding.emb^-injective ∘ₚ-id-embedding
