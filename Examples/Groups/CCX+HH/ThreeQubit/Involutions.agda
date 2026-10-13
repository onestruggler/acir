------------------------------------------------------------------------
-- Presentations of groups
--
-- The eight physical generators are involutions in the Table 1 source.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Involutions where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Word.Base using (ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Main
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open S using (actV ; set₁ ; set₂)

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  checked : (g : Gen 3) → S.⟦ E.e g • E.e g ⟧ᵐ ≡ S.𝕀
  checked X-gen = refl
  checked (X-gen ↥) = refl
  checked (X-gen ↥ ↥) = refl
  checked CX-gen = refl
  checked (CX-gen ↥) = refl
  checked CCX-gen = refl
  checked HH-gen = refl
  checked (HH-gen ↥) = refl
  checked (gate₀ ())
  checked ((gate₀ ()) ↥)
  checked ((gate₀ ()) ↥ ↥)
  checked ((gate₀ ()) ↥ ↥ ↥)

source-involution : (g : Gen 3) → PB._≈_ (T._===_ {8}) (E.e g • E.e g) ε
source-involution g = Main.completeness (checked g)
