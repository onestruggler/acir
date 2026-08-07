------------------------------------------------------------------------
-- Presentations of groups
--
-- Monoid and group homomorphism / monomorphism / isomorphism builders
-- for the extension (f ʷ) and the lift wmap f, together with transfer
-- of normal forms along a generator retraction
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base
open import Level

module Normalization.StarInterp {A : Set} (Γ : WRel A) where

open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)

import Presentation.Base as PB
import Presentation.Properties as PP
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
open PP Γ renaming (•-ε-monoid to monoid₁)

module Extend
  (mon : Monoid 0ℓ 0ℓ)
  (let open Monoid mon renaming (Carrier to C ; ε to εₘ ; _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ ; assoc to assoc₂))
  (⟦_⟧₀ : A -> C)
  where

  ⟦_⟧ : Word A -> C
  ⟦ [ x ]ʷ ⟧ = ⟦ x ⟧₀ 
  ⟦ Word.ε ⟧ = εₘ
  ⟦ a • a₁ ⟧ = ⟦ a ⟧ ∙ ⟦ a₁ ⟧

  -- ⟦_⟧ preserves the free-monoid operations on the nose.
  homo : ∀ x y → ⟦ x • y ⟧ ≈₂ ⟦ x ⟧ ∙ ⟦ y ⟧
  homo x y = refl₂

  ε-homo : ⟦ ε ⟧ ≈₂ εₘ
  ε-homo = refl₂

  module Cong
    ( fʷ-cong-ax : ∀ {w v : Word A} → w ===₁ v → ⟦ w ⟧ ≈₂ ⟦ v ⟧ )
    where

    fʷ-cong : ∀ {w v : Word A} → w ≈₁ v → ⟦ w ⟧ ≈₂ ⟦ v ⟧
    fʷ-cong PB.refl = refl₂
    fʷ-cong (PB.sym eq) = sym₂ (fʷ-cong eq)
    fʷ-cong (PB.trans eq eq₁) = trans₂ (fʷ-cong eq) (fʷ-cong eq₁)
    fʷ-cong (PB.cong eq eq₁) = ∙-cong (fʷ-cong eq) (fʷ-cong eq₁)
    fʷ-cong (PB.assoc {w} {v} {u}) = assoc₂ ⟦ w ⟧ ⟦ v ⟧ ⟦ u ⟧
    fʷ-cong {v = v} PB.left-unit = identityˡ ⟦ v ⟧
    fʷ-cong {v = v} PB.right-unit = identityʳ ⟦ v ⟧
    fʷ-cong (PB.axiom x) = fʷ-cong-ax x

    -- The extension ⟦_⟧ is a monoid homomorphism from the presented
    -- monoid Word A / ≈₁ (= monoid₁) to mon: fʷ-cong is its congruence,
    -- and the operation/unit are preserved definitionally (homo, ε-homo).
    open MonoidMorphisms (Monoid.rawMonoid monoid₁) (Monoid.rawMonoid mon)

    isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
    isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = fʷ-cong }
        ; homo             = homo
        }
      ; ε-homo = ε-homo
      }
