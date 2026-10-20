------------------------------------------------------------------------
-- Presentations of groups
--
-- The invariant that separates the cosets of a pair's setwise
-- stabiliser.
--
-- ψ g records, for each level x, whether g sends x into {p, q}.  A
-- letter b that preserves {p, q} (`keeps b`, decided) leaves ψ unchanged
-- on the left (`ψ-mul`): b • g sends x into {p, q} exactly when g does.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (Fin)

module Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.StabPair (p q : Fin 16) where

open import Data.Bool.Base using (Bool ; true ; false ; _∨_)
open import Data.Vec.Base using (Vec ; map ; lookup)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound ; eqF)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Gamma using (L ; P ; spL ; mul)

inPair : Fin 16 → Bool
inPair x = eqF x p ∨ eqF x q

ψ : P → Vec Bool 16
ψ g = map inPair g

private
  eqB : Bool → Bool → Bool
  eqB true  b = b
  eqB false true  = false
  eqB false false = true

  eqB-sound : ∀ a b → eqB a b ≡ true → a ≡ b
  eqB-sound true  true  _ = Eq.refl
  eqB-sound false false _ = Eq.refl

keeps : L → Bool
keeps b = allFin 16 (λ x → eqB (inPair (lookup (spL b) x)) (inPair x))

ψ-mul : ∀ b → keeps b ≡ true → ∀ g → ψ (mul (spL b) g) ≡ ψ g
ψ-mul b h g = Eq.trans (Eq.sym (VP.map-∘ inPair (lookup (spL b)) g))
  (VP.map-cong (λ x → eqB-sound _ _
    (allFin-sound 16 (λ y → eqB (inPair (lookup (spL b) y)) (inPair y)) h x)) g)
