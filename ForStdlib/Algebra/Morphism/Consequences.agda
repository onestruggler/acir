------------------------------------------------------------------------
-- The Agda standard library
--
-- A monoid homomorphism between two groups is a group homomorphism
--
-- (Staged in ForStdlib for upstreaming into
-- Algebra.Morphism.Consequences.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Morphism.Consequences where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Level using (Level)
import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- A monoid homomorphism between groups preserves inverses, and is
-- therefore a group homomorphism: h (x ⁻¹) is a left inverse of h x
-- (h (x ⁻¹) ∙ h x ≈ h (x ⁻¹ ∙ x) ≈ h ε ≈ ε), and left inverses are
-- unique.  The standard library used to derive this only in the
-- now-deprecated Algebra.Morphism.

module _ (G₁ : Group a ℓ₁) (G₂ : Group b ℓ₂) where

  open Group G₁ using () renaming
    (Carrier to A ; _∙_ to _∙₁_ ; _⁻¹ to _⁻¹₁ ; ε to ε₁ ; inverseˡ to inverseˡ₁)
  open Group G₂ using () renaming
    (Carrier to B ; _∙_ to _∙₂_ ; _⁻¹ to _⁻¹₂ ; ε to ε₂ ; _≈_ to _≈₂_ ; setoid to setoid₂)
  open MonoidMorphisms (Group.rawMonoid G₁) (Group.rawMonoid G₂)
    using (IsMonoidHomomorphism)
  open GroupMorphisms (Group.rawGroup G₁) (Group.rawGroup G₂)
    using (IsGroupHomomorphism)
  open GroupProperties G₂ using (inverseˡ-unique)

  isMonoidHomomorphism⇒isGroupHomomorphism :
    ∀ {h : A → B} → IsMonoidHomomorphism h → IsGroupHomomorphism h
  isMonoidHomomorphism⇒isGroupHomomorphism {h} mono = record
    { isMonoidHomomorphism = mono
    ; ⁻¹-homo              = ⁻¹-homo
    }
    where
    open IsMonoidHomomorphism mono
    open ≈-Reasoning setoid₂

    ⁻¹-homo : ∀ x → h (x ⁻¹₁) ≈₂ (h x) ⁻¹₂
    ⁻¹-homo x = inverseˡ-unique (h (x ⁻¹₁)) (h x) (begin
      h (x ⁻¹₁) ∙₂ h x  ≈⟨ homo (x ⁻¹₁) x ⟨
      h (x ⁻¹₁ ∙₁ x)    ≈⟨ ⟦⟧-cong (inverseˡ₁ x) ⟩
      h ε₁              ≈⟨ ε-homo ⟩
      ε₂                ∎)
