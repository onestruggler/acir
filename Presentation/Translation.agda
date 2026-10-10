------------------------------------------------------------------------
-- Presentations of groups
--
-- A sub-presentation of a presented group translates into the
-- presentation
--
-- Let _===_ (over X) present a subgroup of G, and _≐_ (over Y) present
-- G itself.  Every word over X has a word over Y with the same value,
-- since the second interpretation is onto (`translate`).  Both
-- interpretations are injective, so two words over X are related
-- exactly when their translations are (`translate-≈`), and the
-- translation is a monomorphism from the group that _===_ presents to
-- the one that _≐_ presents (`translate-mono`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Group)
open import Level using (Level)
open import Word.Base using (WRel)
open import Presentation.Definitions
  using (_IsSubPresentationOf_ ; _IsPresentationOf_)

module Presentation.Translation
  {a ℓ : Level} {X Y : Set} {_===_ : WRel X} {_≐_ : WRel Y} {G : Group a ℓ}
  (sub : _===_ IsSubPresentationOf G)
  (pres : _≐_ IsPresentationOf G)
  where

open import Algebra.Morphism.Structures
  using (module GroupMorphisms ; module MonoidMorphisms)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Function.Bundles using (_⇔_ ; mk⇔ ; module Equivalence)

open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Word.Base using (Word ; ε ; _•_)
import Presentation.Base as PB

private
  module S = _IsSubPresentationOf_ sub
  module P = _IsPresentationOf_ pres
  module SM = GroupMorphisms (Group.rawGroup S.GL.•-ε-group) (Group.rawGroup G)
  module PM = GroupMorphisms (Group.rawGroup P.GL.•-ε-group) (Group.rawGroup G)
  open Group G using (sym ; trans ; ∙-cong) renaming (_≈_ to _≈ᴳ_)

  monoᴾ = PM.IsGroupIsomorphism.isGroupMonomorphism P.iso
  homˢ  = SM.IsGroupMonomorphism.isGroupHomomorphism S.mono
  homᴾ  = PM.IsGroupMonomorphism.isGroupHomomorphism monoᴾ

  congˢ = SM.IsGroupHomomorphism.⟦⟧-cong homˢ
  congᴾ = PM.IsGroupHomomorphism.⟦⟧-cong homᴾ
  injˢ  = SM.IsGroupMonomorphism.injective S.mono
  injᴾ  = PM.IsGroupMonomorphism.injective monoᴾ
  surjᴾ = PM.IsGroupIsomorphism.surjective P.iso

------------------------------------------------------------------------
-- The translation

-- A word over Y with the value of w.
translate : Word X → Word Y
translate w = proj₁ (surjᴾ S.⟦ w ⟧)

translate-correct : ∀ w → P.⟦ translate w ⟧ ≈ᴳ S.⟦ w ⟧
translate-correct w = proj₂ (surjᴾ S.⟦ w ⟧) (Group.refl P.GL.•-ε-group)

------------------------------------------------------------------------
-- Two words are related exactly when their translations are

translate-≈ : ∀ {u v} → PB._≈_ _===_ u v ⇔ PB._≈_ _≐_ (translate u) (translate v)
translate-≈ {u} {v} = mk⇔
  (λ e → injᴾ (trans (translate-correct u) (trans (congˢ e) (sym (translate-correct v)))))
  (λ e → injˢ (trans (sym (translate-correct u)) (trans (congᴾ e) (translate-correct v))))

------------------------------------------------------------------------
-- The translation is a monomorphism of the presented groups

module _ where
  open GroupMorphisms (Group.rawGroup S.GL.•-ε-group) (Group.rawGroup P.GL.•-ε-group)
  open MonoidMorphisms (Group.rawMonoid S.GL.•-ε-group) (Group.rawMonoid P.GL.•-ε-group)
    using (IsMonoidHomomorphism)

  private
    homo : ∀ u v → PB._≈_ _≐_ (translate (u • v)) (translate u • translate v)
    homo u v = injᴾ (trans (translate-correct (u • v)) (trans
      (SM.IsGroupHomomorphism.homo homˢ u v)
      (sym (trans (PM.IsGroupHomomorphism.homo homᴾ (translate u) (translate v))
                  (∙-cong (translate-correct u) (translate-correct v))))))

    ε-homo : PB._≈_ _≐_ (translate ε) ε
    ε-homo = injᴾ (trans (translate-correct ε) (trans
      (SM.IsGroupHomomorphism.ε-homo homˢ) (sym (PM.IsGroupHomomorphism.ε-homo homᴾ))))

    isMonoidHomomorphism : IsMonoidHomomorphism translate
    isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = Equivalence.to translate-≈ }
        ; homo = homo
        }
      ; ε-homo = ε-homo
      }

  translate-mono : IsGroupMonomorphism translate
  translate-mono = record
    { isGroupHomomorphism =
        isMonoidHomomorphism⇒isGroupHomomorphism S.GL.•-ε-group P.GL.•-ε-group isMonoidHomomorphism
    ; injective = Equivalence.from translate-≈
    }
