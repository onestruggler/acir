------------------------------------------------------------------------
-- The Agda standard library
--
-- The amalgamated free product of two monoids M and N glued along a
-- common carrier C by maps φ : C → M and ψ : C → N.  Unlike the direct
-- or semidirect product there is no concrete carrier: an element is a
-- word over |M| ⊎ |N| and equality is the least monoid congruence that
--   * multiplies out adjacent letters from the same factor,
--   * deletes the units of either factor, and
--   * glues the two images φ c and ψ c of each c : C.
-- When C is a (sub)monoid and φ, ψ are monoid homomorphisms this is the
-- pushout M *_C N in the category of monoids (take C a common submonoid
-- and φ, ψ its inclusions).
--
-- (Staged in ForStdlib for upstreaming into
-- Algebra.Construct.Amalgamation.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Construct.Amalgamation where

open import Algebra.Bundles using (Monoid; Group)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
import Algebra.Properties.Group as GroupProperties

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------
-- The amalgamation congruence on words over |M| ⊎ |N|

module Impl (M : Monoid a ℓ₁) (N : Monoid b ℓ₂) (C : Setoid c ℓ₃)
            (φ : Setoid.Carrier C → Monoid.Carrier M)
            (ψ : Setoid.Carrier C → Monoid.Carrier N) where
  private
    module M = Monoid M
    module N = Monoid N
    module C = Setoid C

  Letter : Set (a ⊔ b)
  Letter = M.Carrier ⊎ N.Carrier

  Word : Set (a ⊔ b)
  Word = List Letter

  infix 4 _≈_

  -- The least congruence on the free monoid of words carrying the
  -- factor operations and gluing φ c to ψ c.
  data _≈_ : Rel Word (a ⊔ b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    m-cong  : ∀ {x y} → x M.≈ y → (inj₁ x ∷ []) ≈ (inj₁ y ∷ [])
    n-cong  : ∀ {x y} → x N.≈ y → (inj₂ x ∷ []) ≈ (inj₂ y ∷ [])
    m-∙     : ∀ x y → (inj₁ x ∷ inj₁ y ∷ []) ≈ (inj₁ (x M.∙ y) ∷ [])
    n-∙     : ∀ x y → (inj₂ x ∷ inj₂ y ∷ []) ≈ (inj₂ (x N.∙ y) ∷ [])
    m-ε     : (inj₁ M.ε ∷ []) ≈ []
    n-ε     : (inj₂ N.ε ∷ []) ≈ []
    glue    : ∀ {p q} → p C.≈ q → (inj₁ (φ p) ∷ []) ≈ (inj₂ (ψ q) ∷ [])
    refl    : ∀ {xs} → xs ≈ xs
    sym     : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
    trans   : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
    ++-cong : ∀ {xs xs′ ys ys′} → xs ≈ xs′ → ys ≈ ys′ → (xs ++ ys) ≈ (xs′ ++ ys′)

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record { refl = refl ; sym = sym ; trans = trans }

  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → xs ≈ ys
  ≡⇒≈ ≡.refl = refl

  open import Algebra.Structures {A = Word} _≈_ using (IsMonoid)

  isMonoid : IsMonoid _++_ []
  isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence
        ; ∙-cong        = ++-cong
        }
      ; assoc = λ xs ys zs → ≡⇒≈ (++-assoc xs ys zs)
      }
    ; identity = (λ xs → refl) , (λ xs → ≡⇒≈ (++-identityʳ xs))
    }

------------------------------------------------------------------------
-- The monoid amalgamated free product

monoid : (M : Monoid a ℓ₁) (N : Monoid b ℓ₂) (C : Setoid c ℓ₃)
         (φ : Setoid.Carrier C → Monoid.Carrier M)
         (ψ : Setoid.Carrier C → Monoid.Carrier N) →
         Monoid (a ⊔ b) (a ⊔ b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
monoid M N C φ ψ = record
  { Carrier  = Word
  ; _≈_      = _≈_
  ; _∙_      = _++_
  ; ε        = []
  ; isMonoid = isMonoid
  } where open Impl M N C φ ψ

------------------------------------------------------------------------
-- The group amalgamated free product
--
-- When M, N and C are groups and φ, ψ preserve inverses (the φ⁻¹, ψ⁻¹
-- hypotheses — automatic for a group homomorphism), the amalgamated
-- free product is again a group: the inverse of a word reverses it and
-- inverts each letter within its own factor.

module _ (M : Group a ℓ₁) (N : Group b ℓ₂) (C : Group c ℓ₃)
         (φ : Group.Carrier C → Group.Carrier M)
         (ψ : Group.Carrier C → Group.Carrier N)
         (φ⁻¹ : ∀ p → Group._≈_ M (φ (Group._⁻¹ C p)) (Group._⁻¹ M (φ p)))
         (ψ⁻¹ : ∀ p → Group._≈_ N (ψ (Group._⁻¹ C p)) (Group._⁻¹ N (ψ p)))
         where
  private
    module M = Group M
    module N = Group N
    module C = Group C
    module GM = GroupProperties M
    module GN = GroupProperties N

  open Impl M.monoid N.monoid C.setoid φ ψ

  invert : Letter → Letter
  invert (inj₁ x) = inj₁ (x M.⁻¹)
  invert (inj₂ y) = inj₂ (y N.⁻¹)

  infix 8 _⁻¹ᴳ
  _⁻¹ᴳ : Word → Word
  [] ⁻¹ᴳ = []
  (a ∷ as) ⁻¹ᴳ = (as ⁻¹ᴳ) ++ (invert a ∷ [])

  -- Word inverse is an anti-homomorphism for concatenation.
  ⁻¹ᴳ-++ : ∀ xs ys → (xs ++ ys) ⁻¹ᴳ ≡ (ys ⁻¹ᴳ) ++ (xs ⁻¹ᴳ)
  ⁻¹ᴳ-++ [] ys = ≡.sym (++-identityʳ (ys ⁻¹ᴳ))
  ⁻¹ᴳ-++ (a ∷ xs) ys =
    ≡.trans (≡.cong (_++ (invert a ∷ [])) (⁻¹ᴳ-++ xs ys))
            (++-assoc (ys ⁻¹ᴳ) (xs ⁻¹ᴳ) (invert a ∷ []))

  -- A letter cancels its inverse on either side.
  cancelʳ : ∀ a → (a ∷ invert a ∷ []) ≈ []
  cancelʳ (inj₁ x) = trans (m-∙ x (x M.⁻¹)) (trans (m-cong (M.inverseʳ x)) m-ε)
  cancelʳ (inj₂ y) = trans (n-∙ y (y N.⁻¹)) (trans (n-cong (N.inverseʳ y)) n-ε)

  cancelˡ : ∀ a → (invert a ∷ a ∷ []) ≈ []
  cancelˡ (inj₁ x) = trans (m-∙ (x M.⁻¹) x) (trans (m-cong (M.inverseˡ x)) m-ε)
  cancelˡ (inj₂ y) = trans (n-∙ (y N.⁻¹) y) (trans (n-cong (N.inverseˡ y)) n-ε)

  -- Congruence in the right argument of _++_ (left factor fixed).
  ++-congˡ : ∀ zs {xs ys} → xs ≈ ys → (zs ++ xs) ≈ (zs ++ ys)
  ++-congˡ zs h = ++-cong (refl {zs}) h

  inverseʳᴳ : ∀ w → (w ++ w ⁻¹ᴳ) ≈ []
  inverseʳᴳ [] = refl
  inverseʳᴳ (a ∷ as) =
    trans (≡⇒≈ (≡.cong (a ∷_) (≡.sym (++-assoc as (as ⁻¹ᴳ) (invert a ∷ [])))))
    (trans (++-congˡ (a ∷ []) (++-cong (inverseʳᴳ as) refl)) (cancelʳ a))

  inverseˡᴳ : ∀ w → (w ⁻¹ᴳ ++ w) ≈ []
  inverseˡᴳ [] = refl
  inverseˡᴳ (a ∷ as) =
    trans (≡⇒≈ (++-assoc (as ⁻¹ᴳ) (invert a ∷ []) (a ∷ as)))
    (trans (++-congˡ (as ⁻¹ᴳ) (++-cong (cancelˡ a) refl)) (inverseˡᴳ as))

  ⁻¹-congᴳ : ∀ {xs ys} → xs ≈ ys → (xs ⁻¹ᴳ) ≈ (ys ⁻¹ᴳ)
  ⁻¹-congᴳ (m-cong x≈y) = m-cong (M.⁻¹-cong x≈y)
  ⁻¹-congᴳ (n-cong x≈y) = n-cong (N.⁻¹-cong x≈y)
  ⁻¹-congᴳ (m-∙ x y) = trans (m-∙ (y M.⁻¹) (x M.⁻¹)) (m-cong (M.sym (GM.⁻¹-anti-homo-∙ x y)))
  ⁻¹-congᴳ (n-∙ x y) = trans (n-∙ (y N.⁻¹) (x N.⁻¹)) (n-cong (N.sym (GN.⁻¹-anti-homo-∙ x y)))
  ⁻¹-congᴳ m-ε = trans (m-cong GM.ε⁻¹≈ε) m-ε
  ⁻¹-congᴳ n-ε = trans (n-cong GN.ε⁻¹≈ε) n-ε
  ⁻¹-congᴳ (glue {p} {q} p≈q) =
    trans (m-cong (M.sym (φ⁻¹ p)))
    (trans (glue (C.⁻¹-cong p≈q)) (n-cong (ψ⁻¹ q)))
  ⁻¹-congᴳ refl = refl
  ⁻¹-congᴳ (sym h) = sym (⁻¹-congᴳ h)
  ⁻¹-congᴳ (trans h k) = trans (⁻¹-congᴳ h) (⁻¹-congᴳ k)
  ⁻¹-congᴳ (++-cong {xs} {xs′} {ys} {ys′} h k) =
    trans (≡⇒≈ (⁻¹ᴳ-++ xs ys))
    (trans (++-cong (⁻¹-congᴳ k) (⁻¹-congᴳ h))
           (≡⇒≈ (≡.sym (⁻¹ᴳ-++ xs′ ys′))))

  open import Algebra.Structures {A = Word} _≈_ using (IsGroup)

  isGroup : IsGroup _++_ [] _⁻¹ᴳ
  isGroup = record
    { isMonoid = isMonoid
    ; inverse  = inverseˡᴳ , inverseʳᴳ
    ; ⁻¹-cong  = ⁻¹-congᴳ
    }

  group : Group (a ⊔ b) (a ⊔ b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  group = record
    { Carrier = Word
    ; _≈_     = _≈_
    ; _∙_     = _++_
    ; ε       = []
    ; _⁻¹     = _⁻¹ᴳ
    ; isGroup = isGroup
    }
