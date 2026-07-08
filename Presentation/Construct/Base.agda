------------------------------------------------------------------------
-- Presentations of groups
--
-- Transporting normal forms between presentations: adjoining a relation
-- by a union, and pulling normal forms back along monoid mono/iso-
-- morphisms.  The relation constructions themselves now live under
-- Word.Relation.Binary.Construct.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Presentation.Construct.Base where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Word.Relation.Binary.MonoidCongruence as PB
import Word.Relation.Binary.MonoidCongruence.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
open import Word.Base
open import Word.Relation.Binary.Construct.Base using (_∪_ ; module LeftRightCongruence-∪)

------------------------------------------------------------------------
-- Transporting normal forms

-- A normal form for Γ gives a weak normal form for the union Γ ∪ Δ.
anfpₗ : ∀ {A} {Γ Δ : WRel A} {NF : Set} →
        NFBase.NormalFormInjective Γ NF → NFBase.WeakNormalForm (Γ ∪ Δ) NF
anfpₗ {A} {Γ} {Δ} nfp = record
  { anf = nf
  ; anf-injective = λ x → lefts (nf-injective x)
  }
  where
  open SNF.NormalFormInjective nfp
  open LeftRightCongruence-∪ Γ Δ

-- A weak normal form for Γ gives one for the union Γ ∪ Δ.
anfpₗ' : ∀ {A} {Γ Δ : WRel A} {ANF : Set} →
         NFBase.WeakNormalForm Γ ANF → NFBase.WeakNormalForm (Γ ∪ Δ) ANF
anfpₗ' {A} {Γ} {Δ} anfp = record
  { anf = anf
  ; anf-injective = λ x → lefts (anf-injective x)
  }
  where
  open SNF.WeakNormalForm anfp
  open LeftRightCongruence-∪ Γ Δ

-- A normal form for Δ gives a weak normal form for the union Γ ∪ Δ.
anfpᵣ : ∀ {A} {Γ Δ : WRel A} {NF : Set} →
        NFBase.NormalFormInjective Δ NF → NFBase.WeakNormalForm (Γ ∪ Δ) NF
anfpᵣ {A} {Γ} {Δ} nfp = record
  { anf = nf
  ; anf-injective = λ x → rights (nf-injective x)
  }
  where
  open SNF.NormalFormInjective nfp
  open LeftRightCongruence-∪ Γ Δ

-- A weak normal form for Δ gives one for the union Γ ∪ Δ.
anfpᵣ' : ∀ {A} {Γ Δ : WRel A} {ANF : Set} →
         NFBase.WeakNormalForm Δ ANF → NFBase.WeakNormalForm (Γ ∪ Δ) ANF
anfpᵣ' {A} {Γ} {Δ} anfp = record
  { anf = anf
  ; anf-injective = λ x → rights (anf-injective x)
  }
  where
  open SNF.WeakNormalForm anfp
  open LeftRightCongruence-∪ Γ Δ

-- Pull a weak normal form back along a monoid monomorphism between
-- the presented monoids.
mono-anfp : ∀ {A B} {Γ : WRel A} {Δ : WRel B} {ANF : Set} →
  NFBase.WeakNormalForm Δ ANF → (f : Word A → Word B) →
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidMonomorphism (Monoid.rawMonoid m₁)
    ((Monoid.rawMonoid m₂)) f → NFBase.WeakNormalForm Γ ANF
mono-anfp {A} {B} {Γ} {Δ} anfp f mono = record
  { anf = anf ∘ f ; anf-injective = inj }
  where
  open PB Γ renaming (_≈_ to _≈₁_)
  open PB Δ renaming (_≈_ to _≈₂_)
  open SNF.WeakNormalForm anfp
  open MonoidMorphisms.IsMonoidMonomorphism mono
    renaming (injective to f-inj)
  inj : {w v : Word A} → anf (f w) ≡ anf (f v) → w ≈₁ v
  inj {w} {v} eq = f-inj (anf-injective eq)

-- Pull a normal form (without inverse) back along a monoid
-- monomorphism between the presented monoids.
mono-nfp : ∀ {A B} {Γ : WRel A} {Δ : WRel B} {NF : Set} →
  NFBase.NormalFormInjective Δ NF → (f : Word A → Word B) →
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidMonomorphism (Monoid.rawMonoid m₁)
    ((Monoid.rawMonoid m₂)) f → NFBase.NormalFormInjective Γ NF
mono-nfp {A} {B} {Γ} {Δ} nfp f mono = record
  { injection = record { to = nf ∘ f ; cong = nf∘f-cong ; injective = inj } }
  where
  open PB Γ renaming (_≈_ to _≈₁_)
  open PB Δ renaming (_≈_ to _≈₂_)
  open SNF.NormalFormInjective nfp
  open MonoidMorphisms.IsMonoidMonomorphism mono
    renaming (injective to f-inj)
  inj : {w v : Word A} → nf (f w) ≡ nf (f v) → w ≈₁ v
  inj {w} {v} eq = f-inj (nf-injective eq)

  nf∘f-cong : {w v : Word A} → w ≈₁ v → nf (f w) ≡ nf (f v)
  nf∘f-cong {w} {v} eq = nf-cong (⟦⟧-cong eq)

-- Pull a normal form back along a monoid isomorphism between the
-- presented monoids.
iso-nfp' : ∀ {A B} {Γ : WRel A} {Δ : WRel B} {NF : Set} →
  NFBase.NormalForm Δ NF → (f : Word A → Word B) →
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidIsomorphism (Monoid.rawMonoid m₁)
    ((Monoid.rawMonoid m₂)) f → NFBase.NormalForm Γ NF
iso-nfp' {A} {B} {Γ} {Δ} nfp f iso = record
  { rightInverse = record
      { to        = nf ∘ f
      ; from      = f⁻¹ ∘ inv-nf
      ; to-cong   = nf∘f-cong
      ; from-cong = λ { Eq.refl → refl₁ }
      ; inverseʳ  = λ { Eq.refl → f⁻¹∘nf⁻¹∘nf∘f≈id }
      }
  }
  where
  open PB Γ renaming (_≈_ to _≈₁_ ; refl to refl₁)
  open PB Δ renaming (_≈_ to _≈₂_ ; trans to trans₂)
  open SNF.NormalForm nfp
  open MonoidMorphisms.IsMonoidIsomorphism iso
    renaming (injective to f-inj ; surjective to f-surj)

  nf∘f-cong : {w v : Word A} → w ≈₁ v → nf (f w) ≡ nf (f v)
  nf∘f-cong {w} {v} eq = nf-cong (⟦⟧-cong eq)

  f⁻¹ : Word B → Word A
  f⁻¹ x with f-surj x
  ... | (y , _) = y

  f∘f⁻¹≈id : ∀ {x} → f (f⁻¹ x) ≈₂ x
  f∘f⁻¹≈id {x} with f-surj x
  ... | (y , p) = p refl₁

  f⁻¹∘nf⁻¹∘nf∘f≈id : {w : Word A} → f⁻¹ (inv-nf (nf (f w))) ≈₁ w
  f⁻¹∘nf⁻¹∘nf∘f≈id {w} with f-surj (f w)
  ... | (y , p) = f-inj (trans₂ f∘f⁻¹≈id inv-nf∘nf=id)
