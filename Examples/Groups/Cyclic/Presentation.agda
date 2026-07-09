------------------------------------------------------------------------
-- Presentations of groups
--
-- Group homomorphism from the free-group presentation (Word (Gen n) / ≈)
-- to the permutation group Permutation′ n, via the tight semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Cyclic.Presentation where

open import Data.Fin.Permutation using (inverseˡ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (sym ; trans ; cong)

open import Algebra.Bundles using (Group)

open import Presentation.GroupLike

open import Examples.Groups.Cyclic.Syntactics

open import Notations
open import Word.Base


import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions

open import Examples.Groups.Cyclic.Syntactics
open import Examples.Groups.Cyclic.Semantics
open import Examples.Groups.Cyclic.Soundness
open import Data.Fin.Permutation
  using ( Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip
        ; inverseˡ ; inverseʳ ; lift₀ ; lift₀-cong ; remove ; lift₀-remove)
open import Data.Product using (_,_)

open import Data.Nat using (zero ; suc)
open import Data.Fin using (zero ; suc)

import Examples.Groups.Cyclic.Uniqueness as TU
import Examples.Groups.Cyclic.Normalization as SN

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)

open import Normalization.StarPresentation

subpresentation : ∀ {n} -> let open PP ((₁₊ n) Cn,_===_) in
  ((₁₊ n) Cn,_===_) IsSubPresentationOf (Cn-group (₁₊ n))
subpresentation {n} =
  GS.GetSubPresentation.groupSubPres
    (λ { order → order-sound (₁₊ n) })
    (grouplike n) (SN.nfp' (₁₊ n)) (TU.unique-nf (₁₊ n))
  where
  module GS = GroupSem ((₁₊ n) Cn,_===_) (Eq.setoid (SN.NF ((₁₊ n))))
                       (Cn-group (₁₊ n)) (gg {(₁₊ n)})



presentation : ∀ {n} -> let open PP ((₁₊ n) Cn,_===_) in
  ((₁₊ n) Cn,_===_) IsPresentationOf (Cn-group (₁₊ n))
presentation {n} = isPresentationOf subpresentation claim
  where
  open PB ((₁₊ n) Cn,_===_)
  open import Function.Definitions using (Surjective)

  -- The section [_] of the normal form realises every element: ⟦ [ y ] ⟧
  -- ≡ y.  At order 1 (ℤ/1ℤ) this is trivial; at order ≥ 2 it is pow-id.
  nf-sound : ∀ m (y : SN.NF (₁₊ m)) → ⟦_⟧ {₁₊ m} SN.[ y ] ≡ y
  nf-sound zero      zero = refl
  nf-sound (suc m')  y    = TU.pow-id y

  claim : Surjective _≈_ (Group._≈_ ((Cn-group (₁₊ n)))) (⟦_⟧ {(₁₊ n)})
  claim y = SN.[ y ] , λ {z} z≈y → Eq.trans (sound z≈y) (nf-sound n y)
