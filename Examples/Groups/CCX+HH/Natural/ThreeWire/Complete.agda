------------------------------------------------------------------------
-- Presentations of groups
--
-- The natural CCX+HH rules are complete on three wires.
--
-- The three-wire circuit group, W(E8), is the union of 135 cosets of
-- W(D8), the even signed permutations of the eight levels.  W(D8) is
-- presented by 33 relators in nine letters (ThreeWire.D8, through the
-- tower Z2³ < AGL(3,2) < S8 < W(D8)), and every one of them, decoded
-- to a circuit, is derived from the natural rules (Circuit.Relators,
-- with lemmas found by bootstrapped partial coset enumerations); so
-- two decoded words in the nine letters with one matrix are equal
-- (Columns.sp-of-matrix, Decode).  The top table (Circuit.TopTable)
-- writes each circuit as such a word followed by one of 135
-- representatives, by derivations from the natural rules, and the
-- representatives are told apart by their matrices (Circuit.Separate,
-- through ThreeQubit's separation).  CosetExtension concludes.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Complete where

open import Data.Fin.Base using (Fin)
open import Data.Fin using (#_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (RingD)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Letters using (dec)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Decode using (decW ; decode-cong)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Columns using (F9 ; sp-of-matrix)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Separate using (separate)
import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.TopTable as Top
import Examples.Groups.CCX+HH.Natural.ThreeWire.D8 as D8
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Invariants using (ιD)
import Examples.Groups.CCX+HH.Natural.Engine as En
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.Natural.Soundness as NS
import Presentation.CosetExtension as CE

private
  open PB (3 VRel,_===_) using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  ≡→≈ : ∀ {u v : Circuit 3} → u ≡ v → 3 ⊢ u ≈ v
  ≡→≈ Eq.refl = refl

  idʷ : (w : Circuit 3) → ([_]ʷ ʷ) w ≡ w
  idʷ [ g ]ʷ  = Eq.refl
  idʷ ε       = Eq.refl
  idʷ (u • v) = Eq.cong₂ _•_ (idʷ u) (idʷ v)

  E9 : Word (Fin 9) → Word _
  E9 = (λ x → [ ιD x ]ʷ) ʷ

  F9-decW : ∀ l → F9 l ≡ decW (E9 l)
  F9-decW [ x ]ʷ  = Eq.refl
  F9-decW ε       = Eq.refl
  F9-decW (u • v) = Eq.cong₂ _•_ (F9-decW u) (F9-decW v)

  inverse : Circuit 3 → Circuit 3
  inverse [ g ]ʷ  = [ g ]ʷ
  inverse ε       = ε
  inverse (u • v) = inverse v • inverse u

  inverse-right : ∀ w → 3 ⊢ w • inverse w ≈ ε
  inverse-right [ g ]ʷ  = En.invol g
  inverse-right ε       = left-unit
  inverse-right (u • v) =
    trans assoc (trans (cong refl (trans (sym assoc)
      (trans (cong (inverse-right v) refl) left-unit))) (inverse-right u))

  sub-complete : ∀ (l m : Word (Fin 9)) → C.interpret (F9 l) ≡ C.interpret (F9 m) → 3 ⊢ F9 l ≈ F9 m
  sub-complete l m eq = Eq.subst₂ (_⊢_≈_ 3) (Eq.sym (F9-decW l)) (Eq.sym (F9-decW m))
    (decode-cong (D8.complete l m (sp-of-matrix l m eq)))

  rep : Fin 135 → Circuit 3
  rep = Top.rep

  fact : ∀ c x → 3 ⊢ ([_]ʷ ʷ) (rep c) • [ x ]ʷ ≈
                     F9 (proj₁ (Top.h c x)) • ([_]ʷ ʷ) (rep (proj₂ (Top.h c x)))
  fact c x = Eq.subst₂ (_⊢_≈_ 3)
    (Eq.cong (_• [ x ]ʷ) (Eq.sym (idʷ (rep c))))
    (Eq.cong₂ _•_ (Eq.sym (F9-decW (proj₁ (Top.h c x)))) (Eq.sym (idʷ (rep (proj₂ (Top.h c x))))))
    (Top.fact c x)

  separate′ : ∀ c c′ (l m : Word (Fin 9)) →
              C.interpret (F9 l • ([_]ʷ ʷ) (rep c)) ≡ C.interpret (F9 m • ([_]ʷ ʷ) (rep c′)) → c ≡ c′
  separate′ c c′ l m eq = separate c c′ l m
    (Eq.subst₂ (λ a b → C.interpret (F9 l • a) ≡ C.interpret (F9 m • b)) (idʷ (rep c)) (idʷ (rep c′)) eq)

  open CE (3 VRel,_===_) C.interpret _·*·_ (λ _ _ → Eq.refl) NS.sound inverse inverse-right
    {X = Gen 3} {B = Fin 9} {C = Fin 135} [_]ʷ (λ x → ⟪ dec (ιD x) ⟫) sub-complete
    (# 0) rep Eq.refl Top.h fact separate′ using () renaming (complete to complete′)

-- Completeness on three wires.
complete : ∀ {u v : Circuit 3} → C.interpret u ≡ C.interpret v → 3 ⊢ u ≈ v
complete {u} {v} eq = Eq.subst₂ (_⊢_≈_ 3) (idʷ u) (idʷ v)
  (complete′ u v (Eq.subst₂ (λ a b → C.interpret a ≡ C.interpret b) (Eq.sym (idʷ u)) (Eq.sym (idʷ v)) eq))
