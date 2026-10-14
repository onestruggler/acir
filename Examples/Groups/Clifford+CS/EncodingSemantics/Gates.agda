------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level encoding preserves the semantics of every generator
--
-- Each gate's product reads as its form (Diagonal, Kgate), and the
-- form is the operator of the generator (WireForms.gen-form).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.EncodingSemantics.Gates (m : ℕ) where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ᵍ ; ⟦⟧ₒ-gen)
open import Examples.Groups.Clifford+CS.Encoding m
open import Examples.Groups.Clifford+CS.BridgeGray n using (⟦_⟧Y)
open import Examples.Groups.Clifford+CS.EncodingSemantics.WireForms m using (form ; gen-form)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Diagonal m
open import Examples.Groups.Clifford+CS.EncodingSemantics.Kgate m using (E-K-sem)

-- The product of a gate at its position reads as the form there.
eTL′-sem : ∀ (g : Gen n) → ⟦ eTL′ (view g) ⟧Y ~ (1 , form (view g))
eTL′-sem g with view g in eq
... | scalar I-gate = E-I-sem
... | one p S-gate  = E-S-sem p (view-bound₁ g eq)
... | one p K-gate  = E-K-sem p (view-bound₁ g eq)
... | two p CS-gate = E-CS-sem p (view-bound₂ g eq)

-- The two-level encoding of a generator has its matrix.
eTL-sem : ∀ (g : Gen n) → ⟦ eTL g ⟧Y ~ ⟦ [ g ]ʷ ⟧
eTL-sem g =
  ~-trans {s = ⟦ eTL g ⟧Y} {1 , form (view g)} {⟦ [ g ]ʷ ⟧}
    (eTL′-sem g)
    (~-reflexive {l = 1} {1} {form (view g)} {proj₂ ⟦ [ g ]ʷ ⟧} Eq.refl
      (≐-sym (≐-trans (⟦⟧ₒ-gen g) (gen-form g))))
  where open import Data.Product using (proj₂)
