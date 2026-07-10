------------------------------------------------------------------------
-- Presentations of groups
--
-- The symplectic group Sp(2n, ℤ/pℤ) (p prime).
--
-- This is the *semantic* target of the qupit-Clifford presentations in
-- Examples.Groups.Symplectic.* : the group of ℤ/pℤ-linear automorphisms
-- of the phase space (ℤ/pℤ)²ⁿ = Pauli n that preserve the symplectic
-- form sform.  The pieces are collected from the scattered definitions:
--
--   * the phase space  Pauli n            (Examples.Groups.Pauli.Semantics),
--   * the symplectic form  sform          (Examples.Groups.Pauli.Semantics),
--   * "acts symplectically" = linear + sform-preserving; every Clifford
--     circuit acts this way — its action `act` (Action.agda) is linear
--     and preserves sform (Symplectic-Derived.lemma-sform-fix).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Semantics (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Algebra.Bundles    using (Group)
open import Algebra.Structures using (IsGroup)
open import Data.Product using (_,_)
open import Function using (id ; _∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≗_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli ; sform ; _+ₚ_ ; _*ₚ_)

------------------------------------------------------------------------
-- Symplectic transformations
--
-- A symplectic transformation of the n-qupit phase space: a linear
-- automorphism of Pauli n = (ℤ/pℤ)²ⁿ preserving the symplectic form.

record Symplectic (n : ℕ) : Set where
  field
    ap        : Pauli n → Pauli n
    ap⁻¹      : Pauli n → Pauli n
    invˡ      : ∀ p → ap⁻¹ (ap p) ≡ p
    invʳ      : ∀ p → ap (ap⁻¹ p) ≡ p
    linear-+  : ∀ p q → ap (p +ₚ q) ≡ ap p +ₚ ap q
    linear-*  : ∀ k p → ap (k *ₚ p) ≡ k *ₚ ap p
    preserves : ∀ p q → sform (ap p) (ap q) ≡ sform p q

open Symplectic

-- ap is injective (its left inverse is ap⁻¹).
ap-injective : ∀ {n} (S : Symplectic n) {p q} → ap S p ≡ ap S q → p ≡ q
ap-injective S {p} {q} e =
  Eq.trans (Eq.sym (invˡ S p)) (Eq.trans (Eq.cong (ap⁻¹ S) e) (invˡ S q))

------------------------------------------------------------------------
-- Equality: two transformations agree when their actions agree.

infix 4 _≈ˢ_
_≈ˢ_ : ∀ {n} → Symplectic n → Symplectic n → Set
S ≈ˢ T = ap S ≗ ap T

------------------------------------------------------------------------
-- Group operations (under composition)

-- Identity.
εˢ : ∀ {n} → Symplectic n
εˢ = record
  { ap = id ; ap⁻¹ = id
  ; invˡ = λ _ → Eq.refl ; invʳ = λ _ → Eq.refl
  ; linear-+ = λ _ _ → Eq.refl ; linear-* = λ _ _ → Eq.refl
  ; preserves = λ _ _ → Eq.refl
  }

-- Composition (the right transformation acts first).
infixl 7 _∘ˢ_
_∘ˢ_ : ∀ {n} → Symplectic n → Symplectic n → Symplectic n
S ∘ˢ T = record
  { ap   = ap S ∘ ap T
  ; ap⁻¹ = ap⁻¹ T ∘ ap⁻¹ S
  ; invˡ = λ p → Eq.trans (Eq.cong (ap⁻¹ T) (invˡ S (ap T p))) (invˡ T p)
  ; invʳ = λ p → Eq.trans (Eq.cong (ap S) (invʳ T (ap⁻¹ S p))) (invʳ S p)
  ; linear-+ = λ p q →
      Eq.trans (Eq.cong (ap S) (linear-+ T p q)) (linear-+ S (ap T p) (ap T q))
  ; linear-* = λ k p →
      Eq.trans (Eq.cong (ap S) (linear-* T k p)) (linear-* S k (ap T p))
  ; preserves = λ p q →
      Eq.trans (preserves S (ap T p) (ap T q)) (preserves T p q)
  }

-- Inverse (linearity and form-preservation of ap⁻¹ are derived from
-- those of ap using the two round-trip laws).
infix 8 _⁻¹ˢ
_⁻¹ˢ : ∀ {n} → Symplectic n → Symplectic n
S ⁻¹ˢ = record
  { ap = ap⁻¹ S ; ap⁻¹ = ap S
  ; invˡ = invʳ S ; invʳ = invˡ S
  ; linear-+ = inv-linear-+
  ; linear-* = inv-linear-*
  ; preserves = inv-preserves
  }
  where
  inv-preserves : ∀ p q → sform (ap⁻¹ S p) (ap⁻¹ S q) ≡ sform p q
  inv-preserves p q =
    Eq.trans (Eq.sym (preserves S (ap⁻¹ S p) (ap⁻¹ S q)))
             (Eq.cong₂ sform (invʳ S p) (invʳ S q))
  inv-linear-+ : ∀ p q → ap⁻¹ S (p +ₚ q) ≡ ap⁻¹ S p +ₚ ap⁻¹ S q
  inv-linear-+ p q = ap-injective S
    (Eq.trans (invʳ S (p +ₚ q))
      (Eq.sym (Eq.trans (linear-+ S (ap⁻¹ S p) (ap⁻¹ S q))
                        (Eq.cong₂ _+ₚ_ (invʳ S p) (invʳ S q)))))
  inv-linear-* : ∀ k p → ap⁻¹ S (k *ₚ p) ≡ k *ₚ ap⁻¹ S p
  inv-linear-* k p = ap-injective S
    (Eq.trans (invʳ S (k *ₚ p))
      (Eq.sym (Eq.trans (linear-* S k (ap⁻¹ S p))
                        (Eq.cong (k *ₚ_) (invʳ S p)))))

------------------------------------------------------------------------
-- The symplectic group Sp(2n, ℤ/pℤ)

module _ (n : ℕ) where

  Sp-isGroup : IsGroup {A = Symplectic n} _≈ˢ_ _∘ˢ_ εˢ _⁻¹ˢ
  Sp-isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record
            { refl  = λ _ → Eq.refl
            ; sym   = λ e p → Eq.sym (e p)
            ; trans = λ e f p → Eq.trans (e p) (f p)
            }
          ; ∙-cong = λ {S} {_} {T} {T'} e f p →
              Eq.trans (Eq.cong (ap S) (f p)) (e (ap T' p))
          }
        ; assoc = λ _ _ _ _ → Eq.refl
        }
      ; identity = (λ _ _ → Eq.refl) , (λ _ _ → Eq.refl)
      }
    ; inverse = (λ S → invˡ S) , (λ S → invʳ S)
    ; ⁻¹-cong = λ {S} {T} e p → ap-injective T
        (Eq.trans (Eq.trans (Eq.sym (e (ap⁻¹ S p))) (invʳ S p)) (Eq.sym (invʳ T p)))
    }

  Sp-group : Group 0ℓ 0ℓ
  Sp-group = record { isGroup = Sp-isGroup }
