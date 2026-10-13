------------------------------------------------------------------------
-- Presentations of groups
--
-- The all-width circuit calculus as a group sub-presentation of the
-- dyadic orthogonal group.  Its image is characterized in GeneralN/
-- Generation for widths at least four, with finite small-width cases.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Orthogonal where

open import Data.Nat.Base using (ℕ ; _^_)
open import Data.Product.Base using (_,_)
open import Algebra.Bundles using (Group)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Presentation.Definitions
  using (_IsSubMonoidPresentationOf_ ; _IsSubPresentationOf_
        ; subMonoidPresentation⇒subPresentation)
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
open import Examples.Groups.CCX+HH.Presentation
  using (_===_ ; soundness ; completeness ; grouplike)
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S

⟦_⟧ᴼ : ∀ {n} → Circuit n → S.OMat (2 ^ n)
⟦ w ⟧ᴼ = S.⟦ E.encode w ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode w)

submonoidPresentation : ∀ n →
  (_===_ {n}) IsSubMonoidPresentationOf (Group.monoid (S.O (2 ^ n)))
submonoidPresentation n = record
  { ⟦_⟧ = ⟦_⟧ᴼ
  ; mono = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record
          { cong = λ {u} {v} p → Eq.trans (C.encoding-correct u)
              (Eq.trans (soundness p) (Eq.sym (C.encoding-correct v))) }
        ; homo = λ u v → S.⟦•⟧ᵐ (E.encode u) (E.encode v)
        }
      ; ε-homo = refl
      }
    ; injective = λ {u} {v} eq → completeness
        (Eq.trans (Eq.sym (C.encoding-correct u))
          (Eq.trans eq (C.encoding-correct v)))
    }
  }

subpresentationᴼ : ∀ n → (_===_ {n}) IsSubPresentationOf (S.O (2 ^ n))
subpresentationᴼ n = subMonoidPresentation⇒subPresentation
  (submonoidPresentation n) (grouplike n)
