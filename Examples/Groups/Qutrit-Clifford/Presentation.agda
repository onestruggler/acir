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
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Presentation where

open import Algebra.Bundles using (Monoid)
import Algebra.Construct.Flip.Op as Flip
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Unit using (tt)
open import Level using (0ℓ)

open import Presentation.Definitions using (_IsSubMonoidPresentationOf_)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics using (⟦_⟧ ; monoid ; ≈-refl)
open import Examples.Groups.Qutrit-Clifford.Soundness using (sound)
open import Examples.Groups.Qutrit-Clifford.Rels using (Rels ; rels)
open import Examples.Groups.Qutrit-Clifford.Completeness using (completeness)
open import Examples.Groups.Qutrit-Clifford.Box1 using (br₁)
open import Examples.Groups.Qutrit-Clifford.Box2 using (br₂)
open import Examples.Groups.Qutrit-Clifford.Box3 using (br₃)

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
