------------------------------------------------------------------------
-- Presentations of groups
--
-- Word algebra in any presented monoid: conjugates, and words passing
-- one another.  Every lemma is over word variables, so instantiating it
-- never makes Agda compare two spellings of a word by reducing them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (Word ; WRel)

module Examples.Groups.CCX+HH.NaturalP.WordAlg {X : Set} (Γ : WRel X) where

open import Word.Base using (ε ; _•_)
import Presentation.Base as PB
open PB Γ using (_≈_)

private
  variable
    A B C D Y Y⁻ Z Z′ U V : Word X

-- Conjugation by a word that is its own inverse.
cj : Word X → Word X → Word X
cj Z W = Z • (W • Z)

cj-cong : Y ≈ Y⁻ → cj Z Y ≈ cj Z Y⁻
cj-cong e = PB.cong PB.refl (PB.cong e PB.refl)

cj-cj : Z • Z ≈ ε → cj Z (cj Z Y) ≈ Y
cj-cj ZZ =
  PB.trans (PB.cong PB.refl PB.assoc)
  (PB.trans (PB.sym PB.assoc)
  (PB.trans (PB.cong ZZ PB.refl)
  (PB.trans PB.left-unit
  (PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl ZZ) PB.right-unit)))))

cj-• : Z • Z ≈ ε → cj Z (U • V) ≈ cj Z U • cj Z V
cj-• ZZ = PB.sym
  (PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl PB.assoc)
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong ZZ PB.refl)))
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.left-unit))
    (PB.cong PB.refl (PB.sym PB.assoc)))))))

cj-ε : Z • Z ≈ ε → cj Z ε ≈ ε
cj-ε ZZ = PB.trans (PB.cong PB.refl PB.left-unit) ZZ

-- A word passing Y and Y⁻ moves inside their conjugate.
slide : Z • Y ≈ Y • Z → Z • Y⁻ ≈ Y⁻ • Z →
  Z • ((Y • (C • Y⁻)) • Z) ≈ Y • ((Z • (C • Z)) • Y⁻)
slide ZY ZY⁻ =
  PB.trans (PB.cong PB.refl PB.assoc)
  (PB.trans (PB.sym PB.assoc)
  (PB.trans (PB.cong ZY PB.refl)
  (PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.assoc))
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong PB.refl (PB.sym ZY⁻))))
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
    (PB.cong PB.refl (PB.sym PB.assoc))))))))

-- B commuting with C and cancelling against D drops out:
-- (A B) (C (D E)) = A (C E).
cancel-mid : ∀ {E} → C • B ≈ B • C → B • D ≈ ε →
  (A • B) • (C • (D • E)) ≈ A • (C • E)
cancel-mid CB BD =
  PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
  (PB.trans (PB.cong PB.refl (PB.cong (PB.sym CB) PB.refl))
  (PB.trans (PB.cong PB.refl PB.assoc)
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong BD PB.refl)))
    (PB.cong PB.refl (PB.cong PB.refl PB.left-unit)))))))
