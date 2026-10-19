------------------------------------------------------------------------
-- Presentations of groups
--
-- The presentation of W(D8) by the tower relators, decoded into
-- Natural on three wires.
--
-- Every relator decodes to a derivation of Natural (Relators), so every
-- derivation of the tower relators does (`decode-cong`); with the
-- completeness of the tower for W(D8) (ThreeWire.D8), two words in the
-- nine letters with one signed permutation decode to equal circuits
-- (`d8nat`, an equation for the generated derivations).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Decode where

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Letters
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Relators using (relN ; relN-lhs ; relN-rhs)
import Examples.Groups.CCX+HH.Natural.Engine as En
import Examples.Groups.CCX+HH.Natural.ThreeWire.Pure as Pu
import Examples.Groups.CCX+HH.Natural.ThreeWire.Gamma as Γm
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Invariants using (ιD)
import Examples.Groups.CCX+HH.Natural.ThreeWire.D8 as D8

open PB (3 VRel,_===_) using (refl ; sym ; trans ; cong ; left-unit ; right-unit)

private
  ≡→≈ : ∀ {u v : Circuit 3} → u ≡ v → 3 ⊢ u ≈ v
  ≡→≈ Eq.refl = refl

-- A word in the nine letters, decoded.
decW : Word Γm.L → Circuit 3
decW = (λ a → ⟪ dec a ⟫) ʷ

-- Decoding a list is reading the concatenation of the decoded letters.
decW-list : (xs : List Γm.L) → 3 ⊢ decW (Γm.⟪ xs ⟫) ≈ ⟪ concatMap dec xs ⟫
decW-list []       = refl
decW-list (x ∷ xs) = trans (cong refl (decW-list xs))
  (sym (En.⟪++⟫ (dec x) (concatMap dec xs)))

private
  rel-nat : ∀ r → 3 ⊢ decW (Γm.⟪ Γm.relator r ⟫) ≈ ε
  rel-nat r = trans (decW-list (Γm.relator r))
    (trans (≡→≈ (Eq.cong ⟪_⟫ (Eq.sym (relN-lhs r))))
      (trans (prf (relN r)) (≡→≈ (Eq.cong ⟪_⟫ (relN-rhs r)))))

  wd : ∀ {w v} → w Γm.Γ v → 3 ⊢ decW w ≈ decW v
  wd (Γm.rel r) = rel-nat r

decode-cong : ∀ {w v : Word Γm.L} → w Pu.≈ v → 3 ⊢ decW w ≈ decW v
decode-cong = PP.StarCongruence.fʷ-cong Γm._Γ_ (3 VRel,_===_) (λ a → ⟪ dec a ⟫) wd

------------------------------------------------------------------------
-- W(D8), complete in Natural

private
  E9 : Word (Fin 9) → Word Γm.L
  E9 = (λ x → [ ιD x ]ʷ) ʷ

  decE9 : (u : List (Fin 9)) → 3 ⊢ decW (E9 (Pu.word-of-list u)) ≈ ⟪ concatMap (λ x → dec (ιD x)) u ⟫
  decE9 []       = refl
  decE9 (x ∷ xs) = trans (cong refl (decE9 xs))
    (sym (En.⟪++⟫ (dec (ιD x)) (concatMap (λ x → dec (ιD x)) xs)))

d8nat : (u v : List (Fin 9)) → Γm.sp (Γm.⟪ map ιD u ⟫) ≡ Γm.sp (Γm.⟪ map ιD v ⟫) → Eqn 3
d8nat u v h = eqn (concatMap (λ x → dec (ιD x)) u) (concatMap (λ x → dec (ιD x)) v)
  (trans (sym (decE9 u)) (trans (decode-cong (D8.complete (Pu.word-of-list u) (Pu.word-of-list v) h′))
    (decE9 v)))
  where
  h′ : Γm.sp (E9 (Pu.word-of-list u)) ≡ Γm.sp (E9 (Pu.word-of-list v))
  h′ = Eq.subst₂ (λ a b → Γm.sp a ≡ Γm.sp b) (Pu.⟪map⟫ ιD u) (Pu.⟪map⟫ ιD v) h
