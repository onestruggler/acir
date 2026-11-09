------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness on four wires from the presentation of A₁₆
--
-- The four-wire circuits act on the 16 states as even permutations, and
-- EvenRS 16 presents A₁₆ by symbols γ c d, each a product of two
-- transpositions of numbered states, and the relations _RS,_===_.  So,
-- as ByCoxeter does from S_N's presentation: if the states are
-- numbered (enc, with a left inverse dec), every symbol has a word of
-- placed letters that realises it (R, R-act), the relations hold for
-- those words (R-rel), and every placed letter is a word in the
-- symbols (tw, tw-ok), then two words of placed letters with the same
-- function are equal.
--
-- Realisation (R, R-act) gives the realisation of a word of symbols
-- (R*, a homomorphism: R*-act) and the semantics of the two sides of a
-- relation (rel-sem, from EvenRS.rs-sound-sem), which is what a
-- faithful subgroup needs to decide a relation; Complete adds the
-- relations and the translation of the letters.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.ByEvenRS where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Data.List.Properties using (++-assoc ; ++-identityʳ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

import Examples.Groups.Symmetric.Interpretation as SymI

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (Bits ; Fun ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans ; _⨾_ ; ⨾-cong ; sound)
open import Examples.Groups.XCXCCX-4bit.Placed using (PG ; ι ; ι* ; ⟦_⟧ᵖ* ; ι*-sem)
open import Examples.Groups.XCXCCX-4bit.ToPlaced using (ι*-++)
import Examples.Groups.XCXCCX-4bit.EvenRS as ERS

open ERS 16 using (Sch ; f ; _RS,_===_ ; rs-complete ; rs-sound-sem)

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

private
  ι*-≡ : {xs ys : List PG} → xs ≡ ys → 4 ⊢ ι* xs ≈ ι* ys
  ι*-≡ Eq.refl = refl

  ⟦⟧-++ : (xs ys : List PG) → ⟦ xs ++ ys ⟧ᵖ* ≐ (⟦ xs ⟧ᵖ* ⨾ ⟦ ys ⟧ᵖ*)
  ⟦⟧-++ []       ys x = Eq.refl
  ⟦⟧-++ (g ∷ xs) ys x = ⟦⟧-++ xs ys _

------------------------------------------------------------------------
-- Realising the symbols

module Realisation
  (enc : Fin 16 → Bits 4) (dec : Bits 4 → Fin 16)
  (dec-enc : ∀ i → dec (enc i) ≡ i) (enc-dec : ∀ x → enc (dec x) ≡ x)
  (R : Sch → List PG)
  (R-act : ∀ (x : Sch) (i : Fin 16) → ⟦ R x ⟧ᵖ* (enc i) ≡ enc (SymI.⟦ f x ⟧ ⟨$⟩ʳ i))
  where

  -- The realisation of a word of symbols.
  R* : Word Sch → List PG
  R* [ x ]ʷ   = R x
  R* ε       = []
  R* (u • v) = R* u ++ R* v

  R*-act : (w : Word Sch) (i : Fin 16) → ⟦ R* w ⟧ᵖ* (enc i) ≡ enc (SymI.⟦ (f ʷ) w ⟧ ⟨$⟩ʳ i)
  R*-act [ x ]ʷ   i = R-act x i
  R*-act ε       i = Eq.refl
  R*-act (u • v) i =
    Eq.trans (⟦⟧-++ (R* u) (R* v) (enc i))
      (Eq.trans (Eq.cong ⟦ R* v ⟧ᵖ* (R*-act u i)) (R*-act v (SymI.⟦ (f ʷ) u ⟧ ⟨$⟩ʳ i)))

  -- Two words of symbols whose Coxeter words have the same permutation
  -- have realisations with the same function.
  R*-sem : (u v : Word Sch) → (∀ i → SymI.⟦ (f ʷ) u ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ (f ʷ) v ⟧ ⟨$⟩ʳ i) →
           ⟦ R* u ⟧ᵖ* ≐ ⟦ R* v ⟧ᵖ*
  R*-sem u v e x =
    Eq.trans (Eq.cong ⟦ R* u ⟧ᵖ* (Eq.sym (enc-dec x)))
      (Eq.trans (R*-act u (dec x))
        (Eq.trans (Eq.cong enc (e (dec x)))
          (Eq.trans (Eq.sym (R*-act v (dec x))) (Eq.cong ⟦ R* v ⟧ᵖ* (enc-dec x)))))

  -- The two sides of a relation have realisations with the same
  -- function.
  rel-sem : {u v : Word Sch} → _RS,_===_ u v → ⟦ R* u ⟧ᵖ* ≐ ⟦ R* v ⟧ᵖ*
  rel-sem {u} {v} r = R*-sem u v (rs-sound-sem r)

  -- Completeness, given the relations and the letters as words in the
  -- symbols.
  module Complete
    (R-rel : ∀ {u v} → _RS,_===_ u v → 4 ⊢ ι* (R* u) ≈ ι* (R* v))
    (tw : PG → Word Sch)
    (tw-ok : ∀ g → 4 ⊢ ι g ≈ ι* (R* (tw g)))
    where

    R*-cong : {u v : Word Sch} → PB._≈_ _RS,_===_ u v → 4 ⊢ ι* (R* u) ≈ ι* (R* v)
    R*-cong PB.refl                    = refl
    R*-cong (PB.sym e)                 = sym (R*-cong e)
    R*-cong (PB.trans e e′)            = trans (R*-cong e) (R*-cong e′)
    R*-cong (PB.cong {w = x} {w' = x′} {v = y} {v' = y′} e e′) =
      trans (ι*-++ (R* x) (R* y))
        (trans (cong (R*-cong e) (R*-cong e′)) (sym (ι*-++ (R* x′) (R* y′))))
    R*-cong (PB.assoc {w = x} {v = y} {u = z}) = ι*-≡ (++-assoc (R* x) (R* y) (R* z))
    R*-cong PB.left-unit               = refl
    R*-cong (PB.right-unit {w = x}) = ι*-≡ (++-identityʳ (R* x))
    R*-cong (PB.axiom r)               = R-rel r

    translate : List PG → Word Sch
    translate []      = ε
    translate (g ∷ u) = tw g • translate u

    translate-ok : (u : List PG) → 4 ⊢ ι* u ≈ ι* (R* (translate u))
    translate-ok []      = refl
    translate-ok (g ∷ u) =
      trans (cong (tw-ok g) (translate-ok u)) (sym (ι*-++ (R* (tw g)) (R* (translate u))))

    -- Two words of placed letters with the same function are equal.
    complete : (u v : List PG) → ⟦ u ⟧ᵖ* ≐ ⟦ v ⟧ᵖ* → 4 ⊢ ι* u ≈ ι* v
    complete u v e =
      trans (translate-ok u)
        (trans (R*-cong (rs-complete (translate u) (translate v) same-perm))
               (sym (translate-ok v)))
      where
      at : (w : List PG) (i : Fin 16) →
           ⟦ w ⟧ᵖ* (enc i) ≡ enc (SymI.⟦ (f ʷ) (translate w) ⟧ ⟨$⟩ʳ i)
      at w i =
        Eq.trans (Eq.sym (ι*-sem w (enc i)))
          (Eq.trans (sound (translate-ok w) (enc i))
            (Eq.trans (ι*-sem (R* (translate w)) (enc i)) (R*-act (translate w) i)))
      same-perm : ∀ i → SymI.⟦ (f ʷ) (translate u) ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ (f ʷ) (translate v) ⟧ ⟨$⟩ʳ i
      same-perm i = Eq.trans (Eq.sym (dec-enc _))
        (Eq.trans (Eq.cong dec (Eq.trans (Eq.sym (at u i)) (Eq.trans (e (enc i)) (at v i))))
                  (dec-enc _))
