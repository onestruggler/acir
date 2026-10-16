------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of Figure 1 present the qutrit Clifford circuits' values
--
-- The value of a circuit (Semantics) is its matrix with the factors
-- 1/√3 counted apart, compared exactly; values form a monoid, products
-- in diagram order, so a word in operator order is read into the
-- opposite monoid (values n).  Soundness is the congruence of the
-- reading, completeness its injectivity: the 18 rules are a monoid
-- presentation of the values of n-qutrit Clifford circuits, given the
-- box relations on n qutrits, and so outright at every width (the
-- relations on one, two and three qutrits are derived in Box1, Box2 and
-- Box3).
--
-- Every gate has an inverse word (Syntactics.grouplike), so this is
-- also a group presentation, in two forms (Presentation.Units): the
-- rules present the n-qutrit Clifford group, the circuits compared by
-- their values (presentationᴳ), which has 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ − 1) 9ᵏ
-- elements (clifford-group-order); and they are a sub-presentation of
-- the group of invertible n-qutrit values (subpresentationᵁ).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Presentation where

open import Algebra.Bundles using (Group ; Monoid)
import Algebra.Construct.Flip.Op as Flip
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Unit using (tt)
open import Function.Bundles using (Inverse)
import Function.Construct.Composition as Compose
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Presentation.Definitions
  using (_IsSubMonoidPresentationOf_ ; _IsSubPresentationOf_ ; _IsPresentationOf_)
open import Presentation.Units
  using (Units ; units-subpresentation ; generated ; generated-presentation)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics using (⟦_⟧ ; monoid ; ≈-refl)
open import Examples.Groups.Qutrit-Clifford.Soundness using (sound)
open import Examples.Groups.Qutrit-Clifford.Rels using (Rels ; rels)
open import Examples.Groups.Qutrit-Clifford.Completeness using (completeness)
open import Examples.Groups.Qutrit-Clifford.Box1 using (br₁)
open import Examples.Groups.Qutrit-Clifford.Box2 using (br₂)
open import Examples.Groups.Qutrit-Clifford.Box3 using (br₃)
open import Examples.Groups.Qutrit-Clifford.Count using (order)
open import Examples.Groups.Qutrit-Clifford.Order using (Clifford-setoid ; clifford-order)

private
  variable
    n : ℕ

-- The values on n qutrits, multiplied in operator order.
values : ℕ → Monoid 0ℓ 0ℓ
values n = Flip.monoid (monoid n)

presentation : Rels n → (n VRel,_===_) IsSubMonoidPresentationOf values n
presentation rs = record
  { ⟦_⟧ = ⟦_⟧
  ; mono = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = sound }
        ; homo = λ w v → ≈-refl {s = ⟦ w • v ⟧}
        }
      ; ε-homo = ≈-refl {s = ⟦ ε ⟧}
      }
    ; injective = completeness rs
    }
  }
  where open import Word.Base using (_•_ ; ε)

presentation₀ : (0 VRel,_===_) IsSubMonoidPresentationOf values 0
presentation₀ = presentation tt

presentation₁ : (1 VRel,_===_) IsSubMonoidPresentationOf values 1
presentation₁ = presentation br₁

presentation₂ : (2 VRel,_===_) IsSubMonoidPresentationOf values 2
presentation₂ = presentation (br₁ , br₂)

-- The 18 rules present the values of n-qutrit Clifford circuits, for
-- every n.
presentationⁿ : (n : ℕ) → (n VRel,_===_) IsSubMonoidPresentationOf values n
presentationⁿ n = presentation (rels br₁ br₂ br₃ n)

------------------------------------------------------------------------
-- The group versions

-- The n-qutrit Clifford group: the circuits, compared by their values,
-- with products and inverses of words.  Its setoid is Order's
-- Clifford-setoid.
Clifford : ℕ → Group 0ℓ 0ℓ
Clifford n = generated (presentationⁿ n) grouplike

-- The 18 rules present the n-qutrit Clifford group, for every n.
presentationᴳ : (n : ℕ) → (n VRel,_===_) IsPresentationOf Clifford n
presentationᴳ n = generated-presentation (presentationⁿ n) grouplike

-- It has 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ − 1) 9ᵏ elements.
clifford-group-order : (n : ℕ) → Inverse (Group.setoid (Clifford n)) (Eq.setoid (Fin (order n)))
clifford-group-order n = Compose.inverse same (clifford-order {n})
  where
  same : Inverse (Group.setoid (Clifford n)) (Clifford-setoid n)
  same = record
    { to        = λ w → w
    ; from      = λ w → w
    ; to-cong   = λ e → e
    ; from-cong = λ e → e
    ; inverse   = (λ e → e) , (λ e → e)
    }

-- The 18 rules are a sub-presentation of the group of invertible
-- n-qutrit values, for every n.
subpresentationᵁ : (n : ℕ) → (n VRel,_===_) IsSubPresentationOf Units (values n)
subpresentationᵁ n = units-subpresentation {M = values n} (presentationⁿ n) grouplike
