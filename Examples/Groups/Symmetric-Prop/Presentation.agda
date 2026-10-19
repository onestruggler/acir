------------------------------------------------------------------------
-- Presentations of groups
--
-- The free PROP on no generators presents Sₙ
--
-- Symmetric's theorems, carried along Iso: the identity is an
-- isomorphism from the PROP's word group onto the PRO's, so composing
-- it with Symmetric's (sub-)presentation gives the PROP's; soundness
-- and completeness of the two semantics go through prop⇒pro and
-- pro⇒prop, the congruences being the same.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric-Prop.Presentation where

open import Algebra.Bundles using (Group)
open import Algebra.Bundles.Raw using (RawGroup)
import Algebra.Morphism.Construct.Composition as MC
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ)
open import Function using (_∘_ ; id)
open import Function.Definitions using (Congruent ; Injective)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_)
import Presentation.Properties as PP

open import Examples.Groups.Symmetric-Prop.Syntactics
open import Examples.Groups.Symmetric-Prop.Iso

open import Examples.Groups.Symmetric.Semantics using (Permutation′-group)
open import Examples.Groups.Symmetric.Interpretation using (⟦_⟧)
import Examples.Groups.Symmetric.Presentation as PRO
import Examples.Groups.Symmetric.Soundness as PROˢ
import Examples.Groups.Symmetric.Completeness as PROᶜ
import Examples.Groups.Symmetric.SubPresentation.Semantics as Endo
import Examples.Groups.Symmetric.SubPresentation.SubPres as PROᴱ

------------------------------------------------------------------------
-- The permutation semantics

-- Every derivable equation holds of the permutations ...
sound : ∀ {n} {w v : Circuit n} → n ⊢ w ≈ v →
        ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ ⟦ v ⟧ ⟨$⟩ʳ k
sound {n} e = PROˢ.sound (prop⇒pro n e)

-- ... and two circuits with the same permutation are equal.
completeness : ∀ {n} → let open PP (n VRel,_===_) in
  Injective (Setoid._≈_ word-setoid)
            (Setoid._≈_ (Group.setoid (Permutation′-group n))) ⟦_⟧
completeness {n} e = pro⇒prop n (PROᶜ.completeness e)

private
  module Build (n : ℕ) where

    module P = _IsPresentationOf_ (PRO.presentation {n})
    module S = _IsSubPresentationOf_ (PRO.subpresentation {n})

    G = Permutation′-group n

    ≈-trans : Transitive (RawGroup._≈_ (Group.rawGroup G))
    ≈-trans {x} {y} {z} = Setoid.trans (Group.setoid G) {x} {y} {z}

    module M₁₂ = GroupMorphisms (Group.rawGroup (W.•-ε-group n))
                                (Group.rawGroup (Wᴾ.•-ε-group n))

    iso : GroupMorphisms.IsGroupIsomorphism
            (Group.rawGroup (W.•-ε-group n)) (Group.rawGroup G) (P.⟦_⟧ ∘ id)
    iso = MC.isGroupIsomorphism {G₁ = Group.rawGroup (W.•-ε-group n)}
                                {G₂ = Group.rawGroup (Wᴾ.•-ε-group n)}
                                {G₃ = Group.rawGroup G}
                                (λ {x} {y} {z} → ≈-trans {x} {y} {z})
                                {f = id} {g = P.⟦_⟧} (prop≅pro n) P.iso

    mono : GroupMorphisms.IsGroupMonomorphism
             (Group.rawGroup (W.•-ε-group n)) (Group.rawGroup G) (S.⟦_⟧ ∘ id)
    mono = MC.isGroupMonomorphism {G₁ = Group.rawGroup (W.•-ε-group n)}
                                  {G₂ = Group.rawGroup (Wᴾ.•-ε-group n)}
                                  {G₃ = Group.rawGroup G}
                                  (λ {x} {y} {z} → ≈-trans {x} {y} {z})
                                  {f = id} {g = S.⟦_⟧}
                                  (M₁₂.IsGroupIsomorphism.isGroupMonomorphism (prop≅pro n))
                                  S.mono

-- The PROP with the transposition as its swap, and no relation of its
-- own, presents Sₙ ...
presentation : ∀ {n} → (n VRel,_===_) IsPresentationOf (Permutation′-group n)
presentation {n} = record
  { gl  = grouplike
  ; ⟦_⟧ = Build.P.⟦_⟧ n ∘ id
  ; iso = Build.iso n
  }

-- ... and, read without surjectivity, embeds its word group in it.
subpresentation : ∀ {n} → (n VRel,_===_) IsSubPresentationOf (Permutation′-group n)
subpresentation {n} = record
  { gl   = grouplike
  ; ⟦_⟧  = Build.S.⟦_⟧ n ∘ id
  ; mono = Build.mono n
  }

------------------------------------------------------------------------
-- The endofunction semantics: a setoid embedding

endo-soundness : ∀ n → let open PP (n VRel,_===_) in
  Congruent (Setoid._≈_ word-setoid) (Setoid._≈_ (Endo.Endo-setoid n)) Endo.⟦_⟧
endo-soundness n e = PROᴱ.soundness n (prop⇒pro n e)

endo-completeness : ∀ n → let open PP (n VRel,_===_) in
  Injective (Setoid._≈_ word-setoid) (Setoid._≈_ (Endo.Endo-setoid n)) Endo.⟦_⟧
endo-completeness n e = pro⇒prop n (PROᴱ.completeness n e)
