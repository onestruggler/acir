------------------------------------------------------------------------
-- Presentations of groups
--
-- Permutations of the sixteen levels compared by one boolean, and the
-- norm decision of a tower level as a certificate needs it: two words
-- over the level below with one permutation (`normOK`), equal by that
-- level's completeness (`normOK-sound`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.EqP where

open import Data.Bool.Base using (Bool ; true)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List ; map)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; _ʷ)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound ; eqF ; eqF-sound)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Pure
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Perm 16 using (vec-ext)

eqP : P → P → Bool
eqP u v = allFin 16 (λ i → eqF (lookup u i) (lookup v i))

eqP-sound : ∀ u v → eqP u v ≡ true → u ≡ v
eqP-sound u v h = vec-ext λ i → eqF-sound _ _ (allFin-sound 16 (λ i → eqF (lookup u i) (lookup v i)) h i)

module Norm {nB : ℕ} (ιB : Fin nB → L)
  (lower : ∀ (l m : Word (Fin nB)) →
           sp (((λ b → [ ιB b ]ʷ) ʷ) l) ≡ sp (((λ b → [ ιB b ]ʷ) ʷ) m) →
           ((λ b → [ ιB b ]ʷ) ʷ) l ≈ ((λ b → [ ιB b ]ʷ) ʷ) m) where

  normOK : List (Fin nB) → List (Fin nB) → Bool
  normOK u v = eqP (sp ⟪ map ιB u ⟫) (sp ⟪ map ιB v ⟫)

  normOK-sound : ∀ u v → normOK u v ≡ true → ⟪ map ιB u ⟫ ≈ ⟪ map ιB v ⟫
  normOK-sound u v h =
    trans (≡→≈ (⟪map⟫ ιB u)) (trans (lower (word-of-list u) (word-of-list v) h′)
      (≡→≈ (Eq.sym (⟪map⟫ ιB v))))
    where
    open import Presentation.Base _Γ_ using (trans ; refl)
    ≡→≈ : ∀ {x y : Word L} → x ≡ y → x ≈ y
    ≡→≈ Eq.refl = refl
    h′ : sp (((λ b → [ ιB b ]ʷ) ʷ) (word-of-list u)) ≡ sp (((λ b → [ ιB b ]ʷ) ʷ) (word-of-list v))
    h′ = Eq.subst₂ (λ a b → sp a ≡ sp b) (⟪map⟫ ιB u) (⟪map⟫ ιB v)
           (eqP-sound (sp ⟪ map ιB u ⟫) (sp ⟪ map ιB v ⟫) h)
