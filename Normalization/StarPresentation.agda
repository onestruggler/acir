------------------------------------------------------------------------
-- Presentations of groups
--
-- Monoid and group homomorphism / monomorphism / isomorphism builders
-- for the extension (f ʷ) and the lift wmap f, together with transfer
-- of normal forms along a generator retraction
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base
open import Relation.Binary using (Setoid)
open import Level

module Normalization.StarPresentation {A : Set} (Γ : WRel A) (NF : Setoid 0ℓ 0ℓ) where

open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Base as PB
open import Presentation.GroupLike
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
import Presentation.Properties as PP
open import Normalization.Reidemeister-Schreier
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
open PP Γ renaming (•-ε-monoid to monoid₁)
open import Presentation.Definitions
open import Normalization.NormalForm.Setoid as NFS

module MonoidSem
  (mon : Monoid 0ℓ 0ℓ)
  (let open Monoid mon renaming (Carrier to C ; ε to εₘ ; _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ ; assoc to assoc₂))
  (⟦_⟧₀ : A -> C)
  where

  open import Normalization.StarInterp Γ as SI
  open Extend mon ⟦_⟧₀ public
  
  module GetSubPresentation
    ( fʷ-cong-ax : ∀ {w v : Word A} → w ===₁ v → ⟦ w ⟧ ≈₂ ⟦ v ⟧ )
    {nf-setoid : Setoid 0ℓ 0ℓ}
    (nfp : NormalForm Γ nf-setoid)
    (unfp : UniqueNormalForm Γ nf-setoid (Monoid.setoid mon) ⟦_⟧ nfp)
    where

    open Cong fʷ-cong-ax public

    monoidSubPres : Γ IsSubMonoidPresentationOf mon
    monoidSubPres = record { ⟦_⟧ = ⟦_⟧ ; mono = record { isMonoidHomomorphism = isMonoidHomomorphism ; injective = by-normalization Γ  nf-setoid (Monoid.setoid mon) ⟦_⟧ unfp fʷ-cong } }

------------------------------------------------------------------------
-- Group version
--
-- The same construction targeting a group: reuse MonoidSem on the
-- underlying monoid Group.monoid grp to obtain a monoid
-- sub-presentation, then lift it to a group sub-presentation with
-- subMonoidPresentation⇒subPresentation (a grouplike monoid
-- monomorphism into a group's monoid is a group monomorphism).

module GroupSem
  (grp : Group 0ℓ 0ℓ)
  (⟦_⟧₀ : A → Group.Carrier grp)
  where

  private module MS = MonoidSem (Group.monoid grp) ⟦_⟧₀
  open MS using (⟦_⟧) public

  module GetSubPresentation
    ( fʷ-cong-ax : ∀ {w v : Word A} → w ===₁ v → Group._≈_ grp ⟦ w ⟧ ⟦ v ⟧ )
    ( grouplike  : Grouplike Γ )
    {nf-setoid : Setoid 0ℓ 0ℓ}
    ( nfp  : NormalForm Γ nf-setoid )
    ( unfp : UniqueNormalForm Γ nf-setoid (Group.setoid grp) ⟦_⟧ nfp )
    where

    open MS.GetSubPresentation fʷ-cong-ax nfp unfp using (monoidSubPres)

    groupSubPres : Γ IsSubPresentationOf grp
    groupSubPres = subMonoidPresentation⇒subPresentation monoidSubPres grouplike

