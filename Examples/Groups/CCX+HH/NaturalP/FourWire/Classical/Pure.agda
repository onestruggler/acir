------------------------------------------------------------------------
-- Presentations of groups
--
-- The relators Γ of the four-wire classical tower, as a presentation.
--
-- Γ is sound for the permutations (`sound`), every word has its reverse
-- as an inverse (`inverse-right`, every letter being an involution), and
-- the relators are equations for the rewriting engine (`rel⁼`, `inv⁼`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Pure where

open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Perm 16
  using (mul-assoc ; mul-idˡ ; mul-idʳ)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Gamma public
open import Presentation.Tactics.Words using (module Associative)
open Associative public using (word-of-list)

open PB _Γ_ public using (_≈_)
open PB _Γ_ using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)

open import Presentation.Rewrite _Γ_ eqL eqL-sound public
  using (Eqn ; eqn ; lhs ; rhs ; prf ; sym⁼ ; Step ; rw ; run ; derive ; ⟪++⟫ ; ⟪≈⟫)

------------------------------------------------------------------------
-- Soundness

sound : ∀ {u v} → u ≈ v → sp u ≡ sp v
sound PB.refl        = Eq.refl
sound (PB.sym p)     = Eq.sym (sound p)
sound (PB.trans p q) = Eq.trans (sound p) (sound q)
sound (PB.cong p q)  = Eq.cong₂ mul (sound p) (sound q)
sound (PB.assoc {u} {v} {w}) = mul-assoc (sp u) (sp v) (sp w)
sound (PB.left-unit {w})     = mul-idˡ (sp w)
sound (PB.right-unit {w})    = mul-idʳ (sp w)
sound (PB.axiom (rel r))     = rel-sp r

------------------------------------------------------------------------
-- Relators as equations

rel⁼ : Rel → Eqn
rel⁼ r = eqn (relator r) [] (axiom (rel r))

inv⁼ : L → Eqn
inv⁼ a = rel⁼ (invRel a)

invol : ∀ a → [ a ]ʷ • [ a ]ʷ ≈ ε
invol a = trans (cong refl (sym right-unit))
  (Eq.subst (λ l → ⟪ l ⟫ ≈ ε) (invRel-ok a) (axiom (rel (invRel a))))

------------------------------------------------------------------------
-- Inverses

inverse : Word L → Word L
inverse [ a ]ʷ  = [ a ]ʷ
inverse ε       = ε
inverse (u • v) = inverse v • inverse u

inverse-right : ∀ w → w • inverse w ≈ ε
inverse-right [ a ]ʷ  = invol a
inverse-right ε       = left-unit
inverse-right (u • v) =
  trans assoc (trans (cong refl (trans (sym assoc)
    (trans (cong (inverse-right v) refl) left-unit))) (inverse-right u))

------------------------------------------------------------------------
-- Words of a sub-alphabet

-- Reading a list over a sub-alphabet is reading its image.
⟪map⟫ : ∀ {A : Set} (ι : A → L) (xs : List A) →
        ⟪ map ι xs ⟫ ≡ ((λ a → [ ι a ]ʷ) ʷ) (word-of-list xs)
⟪map⟫ ι []       = Eq.refl
⟪map⟫ ι (x ∷ xs) = Eq.cong ([ ι x ]ʷ •_) (⟪map⟫ ι xs)
