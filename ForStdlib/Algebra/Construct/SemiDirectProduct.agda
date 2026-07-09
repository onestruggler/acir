------------------------------------------------------------------------
-- The Agda standard library
--
-- The semidirect product of two algebraic structures N and H equipped
-- with an action of H on N.  Elements of the new instance are pairs
-- |N| × |H|, but unlike the direct product the first component is
-- twisted by the action when multiplying: in mathematics this is the
-- group N ⋊ H.
--
-- (Staged in ForStdlib for upstreaming into
-- Algebra.Construct.SemiDirectProduct.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Construct.SemiDirectProduct where

open import Algebra.Bundles using (RawMonoid; RawGroup; Monoid; Group)
open import Algebra.Core using (Op₁; Op₂)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (Pointwise; ×-isEquivalence)
open import Level using (Level; _⊔_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Actions

-- An action of H on N: for each h, the map (act h) is an endomorphism
-- of N, and act is itself a monoid homomorphism from H into the monoid
-- of endomorphisms.  These are exactly the laws needed to make the
-- twisted multiplication on N × H associative and unital.

record Action (N : RawMonoid a ℓ₁) (H : RawMonoid b ℓ₂) :
              Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module N = RawMonoid N
    module H = RawMonoid H
  field
    act          : H.Carrier → N.Carrier → N.Carrier
    act-cong     : ∀ {h h′ x x′} → h H.≈ h′ → x N.≈ x′ → act h x N.≈ act h′ x′
    act-ε-homo   : ∀ h → act h N.ε N.≈ N.ε
    act-∙-homo   : ∀ h x y → act h (x N.∙ y) N.≈ act h x N.∙ act h y
    act-identity : ∀ x → act H.ε x N.≈ x
    act-compose  : ∀ h h′ x → act (h H.∙ h′) x N.≈ act h (act h′ x)

------------------------------------------------------------------------
-- Raw bundles

rawMonoid : (N : RawMonoid a ℓ₁) (H : RawMonoid b ℓ₂) →
            (RawMonoid.Carrier H → RawMonoid.Carrier N → RawMonoid.Carrier N) →
            RawMonoid (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawMonoid N H act = record
  { Carrier = N.Carrier × H.Carrier
  ; _≈_     = Pointwise N._≈_ H._≈_
  ; _∙_     = λ (n , x) (m , y) → n N.∙ act x m , x H.∙ y
  ; ε       = N.ε , H.ε
  } where module N = RawMonoid N; module H = RawMonoid H

rawGroup : (N : RawGroup a ℓ₁) (H : RawGroup b ℓ₂) →
           (RawGroup.Carrier H → RawGroup.Carrier N → RawGroup.Carrier N) →
           RawGroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawGroup N H act = record
  { Carrier = N.Carrier × H.Carrier
  ; _≈_     = Pointwise N._≈_ H._≈_
  ; _∙_     = λ (n , x) (m , y) → n N.∙ act x m , x H.∙ y
  ; ε       = N.ε , H.ε
  ; _⁻¹     = λ (n , x) → act (x H.⁻¹) (n N.⁻¹) , x H.⁻¹
  } where module N = RawGroup N; module H = RawGroup H

------------------------------------------------------------------------
-- Bundles

monoid : (N : Monoid a ℓ₁) (H : Monoid b ℓ₂) →
         Action (Monoid.rawMonoid N) (Monoid.rawMonoid H) →
         Monoid (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
monoid N H φ = record
  { Carrier = N.Carrier × H.Carrier
  ; _≈_     = Pointwise N._≈_ H._≈_
  ; _∙_     = _◦_
  ; ε       = N.ε , H.ε
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ×-isEquivalence N.isEquivalence H.isEquivalence
        ; ∙-cong = λ (p₁ , q₁) (p₂ , q₂) →
                     N.∙-cong p₁ (act-cong q₁ p₂) , H.∙-cong q₁ q₂
        }
      ; assoc = assoc◦
      }
    ; identity = identityˡ , identityʳ
    }
  }
  where
  module N = Monoid N
  module H = Monoid H
  open Action φ
  open ≈-Reasoning N.setoid

  _◦_ : Op₂ (N.Carrier × H.Carrier)
  (n , x) ◦ (m , y) = n N.∙ act x m , x H.∙ y

  assoc◦ : ∀ u v w → Pointwise N._≈_ H._≈_ ((u ◦ v) ◦ w) (u ◦ (v ◦ w))
  assoc◦ (n , x) (m , y) (o , z) =
    ( begin
      (n N.∙ act x m) N.∙ act (x H.∙ y) o
        ≈⟨ N.assoc n (act x m) (act (x H.∙ y) o) ⟩
      n N.∙ (act x m N.∙ act (x H.∙ y) o)
        ≈⟨ N.∙-cong N.refl (N.∙-cong N.refl (act-compose x y o)) ⟩
      n N.∙ (act x m N.∙ act x (act y o))
        ≈⟨ N.∙-cong N.refl (N.sym (act-∙-homo x m (act y o))) ⟩
      n N.∙ act x (m N.∙ act y o)
        ∎
    ) , H.assoc x y z

  identityˡ : ∀ u → Pointwise N._≈_ H._≈_ ((N.ε , H.ε) ◦ u) u
  identityˡ (n , x) =
    ( begin
      N.ε N.∙ act H.ε n  ≈⟨ N.∙-cong N.refl (act-identity n) ⟩
      N.ε N.∙ n          ≈⟨ N.identityˡ n ⟩
      n                  ∎
    ) , H.identityˡ x

  identityʳ : ∀ u → Pointwise N._≈_ H._≈_ (u ◦ (N.ε , H.ε)) u
  identityʳ (n , x) =
    ( begin
      n N.∙ act x N.ε  ≈⟨ N.∙-cong N.refl (act-ε-homo x) ⟩
      n N.∙ N.ε        ≈⟨ N.identityʳ n ⟩
      n                ∎
    ) , H.identityʳ x

group : (N : Group a ℓ₁) (H : Group b ℓ₂) →
        Action (Group.rawMonoid N) (Group.rawMonoid H) →
        Group (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
group N H φ = record
  { Carrier = N.Carrier × H.Carrier
  ; _≈_     = Pointwise N._≈_ H._≈_
  ; _∙_     = _◦_
  ; ε       = N.ε , H.ε
  ; _⁻¹     = _⁻¹◦
  ; isGroup = record
    { isMonoid = Monoid.isMonoid (monoid N.monoid H.monoid φ)
    ; inverse  = inverseˡ , inverseʳ
    ; ⁻¹-cong  = λ (p , q) → act-cong (H.⁻¹-cong q) (N.⁻¹-cong p) , H.⁻¹-cong q
    }
  }
  where
  module N = Group N
  module H = Group H
  open Action φ
  open ≈-Reasoning N.setoid

  _◦_ : Op₂ (N.Carrier × H.Carrier)
  (n , x) ◦ (m , y) = n N.∙ act x m , x H.∙ y

  _⁻¹◦ : Op₁ (N.Carrier × H.Carrier)
  (n , x) ⁻¹◦ = act (x H.⁻¹) (n N.⁻¹) , x H.⁻¹

  inverseˡ : ∀ u → Pointwise N._≈_ H._≈_ ((u ⁻¹◦) ◦ u) (N.ε , H.ε)
  inverseˡ (n , x) =
    ( begin
      act (x H.⁻¹) (n N.⁻¹) N.∙ act (x H.⁻¹) n
        ≈⟨ N.sym (act-∙-homo (x H.⁻¹) (n N.⁻¹) n) ⟩
      act (x H.⁻¹) (n N.⁻¹ N.∙ n)
        ≈⟨ act-cong H.refl (N.inverseˡ n) ⟩
      act (x H.⁻¹) N.ε
        ≈⟨ act-ε-homo (x H.⁻¹) ⟩
      N.ε
        ∎
    ) , H.inverseˡ x

  inverseʳ : ∀ u → Pointwise N._≈_ H._≈_ (u ◦ (u ⁻¹◦)) (N.ε , H.ε)
  inverseʳ (n , x) =
    ( begin
      n N.∙ act x (act (x H.⁻¹) (n N.⁻¹))
        ≈⟨ N.∙-cong N.refl (N.sym (act-compose x (x H.⁻¹) (n N.⁻¹))) ⟩
      n N.∙ act (x H.∙ x H.⁻¹) (n N.⁻¹)
        ≈⟨ N.∙-cong N.refl (act-cong (H.inverseʳ x) N.refl) ⟩
      n N.∙ act H.ε (n N.⁻¹)
        ≈⟨ N.∙-cong N.refl (act-identity (n N.⁻¹)) ⟩
      n N.∙ n N.⁻¹
        ≈⟨ N.inverseʳ n ⟩
      N.ε
        ∎
    ) , H.inverseʳ x
