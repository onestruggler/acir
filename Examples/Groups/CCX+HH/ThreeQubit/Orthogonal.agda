------------------------------------------------------------------------
-- Presentations of groups
--
-- The complete three-wire circuit calculus as a group sub-presentation
-- of the dyadic orthogonal group on eight levels.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Orthogonal where

open import Algebra.Bundles using (Group)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Presentation.Definitions
  using (_IsSubMonoidPresentationOf_ ; _IsSubPresentationOf_
        ; subMonoidPresentation⇒subPresentation)
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
open import Examples.Groups.CCX+HH.ThreeQubit.Presentation
  using (_===_ ; grouplike ; module Theory)
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Reduction
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Main

⟦_⟧ᴼ : Circuit 3 → S.OMat 8
⟦ w ⟧ᴼ = S.⟦ E.encode w ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode w)

submonoidPresentation : _===_ IsSubMonoidPresentationOf (Group.monoid (S.O 8))
submonoidPresentation = record
  { ⟦_⟧ = ⟦_⟧ᴼ
  ; mono = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record
          { cong = λ p → Reduction.sound-act (Theory.encode-cong p) S.𝕀 }
        ; homo = λ u v → S.⟦•⟧ᵐ (E.encode u) (E.encode v)
        }
      ; ε-homo = refl
      }
    ; injective = λ eq → Theory.encode-injective (Main.completeness eq)
    }
  }

subpresentationᴼ : _===_ IsSubPresentationOf (S.O 8)
subpresentationᴼ = subMonoidPresentation⇒subPresentation submonoidPresentation grouplike
