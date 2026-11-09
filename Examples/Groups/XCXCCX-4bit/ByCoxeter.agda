------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness at a fixed width from the Coxeter presentation
--
-- Appendix B's argument, for any width k with N = 2ᵏ states.  The
-- states are numbered by an encoding enc : Fin N → Bits k with a left
-- inverse (a Gray code, so that consecutive states differ in one bit),
-- and circuits T d realise the transpositions of consecutive states
-- (T-act).  Given the Coxeter relations for the T d and every gate as a
-- word in them (tw-ok), a circuit is its translation into a Coxeter
-- word (translate-ok), and two circuits with the same function have
-- translations with the same permutation, hence equivalent circuits
-- (Coxeter.Complete.perm-complete′): the theory is complete at width k.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.XCXCCX-4bit.ByCoxeter where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

import Examples.Groups.Symmetric.Interpretation as SymI

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox

module Via
  (k N : ℕ) (T : ℕ → Circuit k)
  (cox : Cox.Circuits.Coxeter N T (k VRel,_===_))
  (enc : Fin N → Bits k) (dec : Bits k → Fin N) (dec-enc : ∀ i → dec (enc i) ≡ i)
  (T-act : ∀ (g : Cox.SG N) (i : Fin N) → ⟦ T (Cox.tr 0 g) ⟧ (enc i) ≡ enc (SymI.⟦ [ g ]ʷ ⟧ ⟨$⟩ʳ i))
  (tw : Gen k → Word (Cox.SG N))
  (tw-ok : ∀ g → k ⊢ [ g ]ʷ ≈ Cox.Circuits.Pc N T 0 (tw g))
  where

  open Cox N using (SG)
  open Cox.Circuits N T using (Pc)
  open Cox.Circuits.Complete N T cox using (perm-complete′)

  -- A Coxeter word's circuit acts on the numbered states as its
  -- permutation.
  Pc-sem : ∀ (p : Word (SG N)) i → ⟦ Pc 0 p ⟧ (enc i) ≡ enc (SymI.⟦ p ⟧ ⟨$⟩ʳ i)
  Pc-sem [ g ]ʷ   i = T-act g i
  Pc-sem ε       i = refl
  Pc-sem (u • v) i =
    Eq.trans (Eq.cong ⟦ Pc 0 v ⟧ (Pc-sem u i)) (Pc-sem v (SymI.⟦ u ⟧ ⟨$⟩ʳ i))

  translate : Circuit k → Word (SG N)
  translate = tw ʷ

  translate-ok : (u : Circuit k) → k ⊢ u ≈ Pc 0 (translate u)
  translate-ok [ g ]ʷ   = tw-ok g
  translate-ok ε       = PB.refl
  translate-ok (u • v) = PB.cong (translate-ok u) (translate-ok v)

  -- Completeness at width k.
  complete : {u v : Circuit k} → ⟦ u ⟧ ≐ ⟦ v ⟧ → k ⊢ u ≈ v
  complete {u} {v} e =
    PB.trans (translate-ok u)
      (PB.trans (perm-complete′ ℕP.≤-refl (translate u) (translate v) same-perm)
                (PB.sym (translate-ok v)))
    where
    at : ∀ (w : Circuit k) i → ⟦ w ⟧ (enc i) ≡ enc (SymI.⟦ translate w ⟧ ⟨$⟩ʳ i)
    at w i = Eq.trans (sound (translate-ok w) (enc i)) (Pc-sem (translate w) i)
    same-perm : ∀ i → SymI.⟦ translate u ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ translate v ⟧ ⟨$⟩ʳ i
    same-perm i = Eq.trans (Eq.sym (dec-enc _))
      (Eq.trans (Eq.cong dec (Eq.trans (Eq.sym (at u i)) (Eq.trans (e (enc i)) (at v i))))
                (dec-enc _))
