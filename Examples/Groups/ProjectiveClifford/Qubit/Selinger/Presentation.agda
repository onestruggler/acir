------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figure 8 modulo scalars presents the Clifford group modulo
-- scalars:
--
--     (n MS.CRel,_===_)  IsPresentationOf  VSp n.
--
-- This is the theorem the scalar layer calls pQ, and the one
-- Selinger.Scalars used to name Complete-mod-scalars.  Both halves of it
-- come from two results already in place, with no new calculation:
--
--   Qubit.Presentation.presentation-n   the EXTENSION relation
--                                       _Clifford,_===_ presents CMS n,
--                                       unconditionally;
--   Selinger.Iso.Iso                    that relation and this one
--                                       present the same group, the
--                                       isomorphism being (f ʷ).
--
-- The bridge between them is that both translations are the identity on
-- gates: a mod-scalar word w sits in the mixed alphabet as [ w ]ᵣ, the
-- extension reads that back as w (embʳ), and (f ʷ) sends it back to w
-- (fᵣ).  So the two directions are
--
--   soundness      w ≈ᵐˢ v  →  [ w ]ᵣ ≈ᶜˡ [ v ]ᵣ  →  w ≈ᶜ v
--   completeness   w ≈ᶜ v   →  [ w ]ᵣ ≈ᶜˡ [ v ]ᵣ  →  w ≈ᵐˢ v
--
-- reading the Iso in its two directions (injective, then ⟦⟧-cong) and
-- the presentation in its two (⟦⟧-cong, then injective).
--
-- The target is the STRUCTURAL model VSp n rather than CMS n, because
-- that is where the scalar layer's projection lands; the two are
-- isomorphic by Qubit.Iso2, and taking the denotation ⟦_⟧ᵛ as this
-- presentation's interpretation is what makes the scalar layer's
-- realisation condition hold by computation rather than by transport.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Selinger.Presentation where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Properties using () renaming (≡-dec to ×-dec)
open import Data.Vec.Properties using () renaming (≡-dec to Vec-dec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
open import Presentation.Construct.Base using ([_]ᵣ)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Morphism using (module GroupMorphism)
open import Normalization.NormalForm.Propositional using (BijectiveNormalForm)
import Normalization.Construction as Con

open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import ForStdlib.Data.Fin.Mod.Prime.Two
  using (p-2 ; p-prime ; g* ; g-gen)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; Circuit)

import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime
  as MS
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.GroupLike
  using (grouplike-MS ; module GL)
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Translation
  using (f ; g)
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Inverse
  using (g-well-defined ; g-left-inv-gen)
import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Iso as SI

open import Examples.Groups.Symplectic.Normalization.Boxes p-2 p-prime using (NF)
open import Examples.Groups.Symplectic.Simplified.Bijective p-2 p-prime g* g-gen
  using (NF-dec)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli)

open import Examples.Groups.ProjectiveClifford.Qubit.Presentation
  using (_Clifford,_===_ ; presentation-n ; bijective-Cl)
import Examples.Groups.ProjectiveClifford.Qubit.ExtensionPresentation as EP
open import Examples.Groups.ProjectiveClifford.Qubit.CliffordGroup
  using (_≈ᶜ_ ; CMS-group)
open import Examples.Groups.ProjectiveClifford.Qubit.Semantics.VSp
  using (Cliff ; _≈ᵛ_ ; εᵛ ; ⟦_⟧ᵛ ; VSp-group)
open import Examples.Groups.ProjectiveClifford.Qubit.Iso2
  using (≈ᵛ-refl ; ≈ᵛ-trans ; ⟦⟧ᵛ-cong ; ⟦⟧ᵛ-injective ; ⟦⟧ᵛ-surjective)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Both translations are the identity on gates
--
-- A mod-scalar word enters the mixed alphabet as [ w ]ᵣ.  The extension
-- reads that back as w, since ⟦_⟧ is the monoid extension of a map
-- sending a gate to its one-letter word; and (f ʷ) sends it back to w,
-- since f leaves a gate alone.  Everything below is these two lemmas
-- used to line up the four implications.

private

  embʳ : (w : Circuit n) → EP.Clifford.⟦_⟧ n [ w ]ᵣ ≡ w
  embʳ [ x ]ʷ  = Eq.refl
  embʳ ε       = Eq.refl
  embʳ (u • v) = Eq.cong₂ _•_ (embʳ u) (embʳ v)

  fᵣ : (w : Circuit n) → (f ʷ) [ w ]ᵣ ≡ w
  fᵣ [ x ]ʷ  = Eq.refl
  fᵣ ε       = Eq.refl
  fᵣ (u • v) = Eq.cong₂ _•_ (fᵣ u) (fᵣ v)

------------------------------------------------------------------------
-- Soundness and completeness of the mod-scalar rule set for the P4
-- action

module _ (n : ℕ) where

  private
    infix 4 _≈ᵐˢ_ _≈ᶜˡ_
    _≈ᵐˢ_ : Circuit n → Circuit n → Set
    _≈ᵐˢ_ = PB._≈_ (n MS.CRel,_===_)

    _≈ᶜˡ_ = PB._≈_ (n Clifford,_===_)

    -- The isomorphism between the two rule sets, read as implications
    -- between their congruences.
    module W-cl = Group-Lemmas (n Clifford,_===_) (GL.grouplike-Cl n)
    module W-ms = Group-Lemmas (n MS.CRel,_===_) grouplike-MS

    module Iso-hom =
      GroupMorphisms.IsGroupIsomorphism (SI.Iso.isGroupIsomorphism n)

    -- ... and the presentation of the extension, likewise.
    module Cl = _IsPresentationOf_ (presentation-n {n})

    module Cl-iso = GroupMorphisms.IsGroupIsomorphism Cl.iso

  -- Soundness: a mod-scalar equality is an equality of P4 actions.
  -- (The two translations are given explicitly: neither (f ʷ) nor the
  -- extension's ⟦_⟧ is invertible by unification, so the words they are
  -- applied to cannot be read back off the goal.)
  sound-ms : {w v : Circuit n} → w ≈ᵐˢ v → w ≈ᶜ v
  sound-ms {w} {v} e =
    Eq.subst₂ _≈ᶜ_ (embʳ w) (embʳ v)
      (Cl-iso.⟦⟧-cong {[ w ]ᵣ} {[ v ]ᵣ}
        (Iso-hom.injective {[ w ]ᵣ} {[ v ]ᵣ}
          (Eq.subst₂ _≈ᵐˢ_ (Eq.sym (fᵣ w)) (Eq.sym (fᵣ v)) e)))

  -- Completeness: equal actions are equal mod scalars.  This is the
  -- input Selinger.Scalars calls Complete-mod-scalars.
  complete-ms : {w v : Circuit n} → w ≈ᶜ v → w ≈ᵐˢ v
  complete-ms {w} {v} e =
    Eq.subst₂ _≈ᵐˢ_ (fᵣ w) (fᵣ v)
      (Iso-hom.⟦⟧-cong {[ w ]ᵣ} {[ v ]ᵣ}
        (Cl-iso.injective {[ w ]ᵣ} {[ v ]ᵣ}
          (Eq.subst₂ _≈ᶜ_ (Eq.sym (embʳ w)) (Eq.sym (embʳ v)) e)))

------------------------------------------------------------------------
-- The presentation
--
-- The interpretation is the VSp denotation, so the homomorphism laws
-- are definitional (concatenation of words is multiplication of pairs)
-- and well-definedness is soundness read through Iso2.⟦⟧ᵛ-cong.
-- Injectivity is Iso2.⟦⟧ᵛ-injective followed by completeness, and
-- surjectivity is Iso2.⟦⟧ᵛ-surjective.

private
  module MH (n : ℕ) =
    MonoidMorphisms (Group.rawMonoid (Group-Lemmas.•-ε-group
                       (n MS.CRel,_===_) grouplike-MS))
                    (Group.rawMonoid (VSp-group n))

  ⟦⟧ᵛ-mono : (n : ℕ) → MH.IsMonoidHomomorphism n (⟦_⟧ᵛ {n})
  ⟦⟧ᵛ-mono n = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = λ {w} {v} e → ⟦⟧ᵛ-cong {n} {w} {v} (sound-ms n e) }
      ; homo = λ w v → ≈ᵛ-refl ⟦ w • v ⟧ᵛ
      }
    ; ε-homo = ≈ᵛ-refl (εᵛ {n})
    }

------------------------------------------------------------------------
-- A bijective normal form for the mod-scalar rule set
--
-- Qubit.Presentation.bijective-Cl gives one for the EXTENSION relation,
-- over the mixed alphabet PauliGen ⊎ Gen.  This rule set is over Gen
-- alone, so the normal form is transported along the translation g —
-- normalise a mod-scalar word by reading it in the mixed alphabet first.
--
-- The three hypotheses of Construction.transport are the isomorphism
-- read in the OTHER direction.  Selinger.Iso builds it for (f ʷ); the
-- builder is symmetric in its two translations, so instantiating it the
-- other way round — g for f, and the four well-definedness / left-
-- inverse witnesses swapped — gives the same isomorphism as (g ʷ),
-- whose congruence, injectivity and surjectivity are exactly what the
-- transport asks for.

private
  module GM' (n : ℕ) where
    open GroupMorphism (n MS.CRel,_===_) (n Clifford,_===_)
           grouplike-MS (GL.grouplike-Cl n)
      using (module StarGroupIsomorphism)
    open StarGroupIsomorphism g f
           g-well-defined g-left-inv-gen SI.f-well-defined SI.f-left-inv-gen
      public using (isGroupIsomorphism)

  module Iso-g (n : ℕ) =
    GroupMorphisms.IsGroupIsomorphism (GM'.isGroupIsomorphism n)

bijective-ms : (n : ℕ) →
               BijectiveNormalForm (n MS.CRel,_===_) (Pauli n × NF n)
bijective-ms n =
  Con.transport (n Clifford,_===_) (n MS.CRel,_===_) (g ʷ)
    (λ {w} {v} → Iso-g.⟦⟧-cong n {w} {v})
    (λ {w} {v} → Iso-g.injective n {w} {v})
    (λ a → proj₁ (Iso-g.surjective n a)
         , proj₂ (Iso-g.surjective n a) PB._≈_.refl)
    bijective-Cl

-- Its normal forms are decidable: a Pauli vector is a Vec of pairs of
-- Fins, and NF-dec decides the symplectic component.
NF-ms-dec : (n : ℕ) → DecidableEquality (Pauli n × NF n)
NF-ms-dec n = ×-dec (Vec-dec (×-dec _≟_ _≟_)) (NF-dec n)

------------------------------------------------------------------------
-- The presentation

presentation-ms : (n : ℕ) → (n MS.CRel,_===_) IsPresentationOf (VSp-group n)
presentation-ms n = record
  { gl  = grouplike-MS
  ; ⟦_⟧ = ⟦_⟧ᵛ
  ; iso = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
          (Group-Lemmas.•-ε-group (n MS.CRel,_===_) grouplike-MS)
          (VSp-group n) (⟦⟧ᵛ-mono n)
      ; injective = λ {w} {v} e → complete-ms n (⟦⟧ᵛ-injective {n} {w} {v} e)
      }
    ; surjective = λ X → proj₁ (⟦⟧ᵛ-surjective X) , λ {z} z≈ →
        ≈ᵛ-trans ⟦ z ⟧ᵛ ⟦ proj₁ (⟦⟧ᵛ-surjective X) ⟧ᵛ X
          (⟦⟧ᵛ-cong {n} {z} {proj₁ (⟦⟧ᵛ-surjective X)} (sound-ms n z≈))
          (proj₂ (⟦⟧ᵛ-surjective X))
    }
  }
