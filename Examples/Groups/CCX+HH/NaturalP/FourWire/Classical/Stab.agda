------------------------------------------------------------------------
-- Presentations of groups
--
-- The invariant that separates the cosets of a point stabiliser.
--
-- ψ g records, for each level x, whether g sends x to p.  A letter b
-- that fixes p (`fixes b`, decided) leaves ψ unchanged on the left
-- (`ψ-mul`): b • g sends x to p exactly when g does.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (Fin)

module Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Stab (p : Fin 16) where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Vec.Base using (Vec ; map ; lookup)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound ; eqF)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Gamma using (L ; P ; spL ; mul)

ψ : P → Vec Bool 16
ψ g = map (λ x → eqF x p) g

private
  eqB : Bool → Bool → Bool
  eqB true  b = b
  eqB false true  = false
  eqB false false = true

  eqB-sound : ∀ a b → eqB a b ≡ true → a ≡ b
  eqB-sound true  true  _ = Eq.refl
  eqB-sound false false _ = Eq.refl

fixes : L → Bool
fixes b = allFin 16 (λ x → eqB (eqF (lookup (spL b) x) p) (eqF x p))

ψ-mul : ∀ b → fixes b ≡ true → ∀ g → ψ (mul (spL b) g) ≡ ψ g
ψ-mul b h g = Eq.trans (Eq.sym (VP.map-∘ (λ x → eqF x p) (lookup (spL b)) g))
  (VP.map-cong (λ x → eqB-sound _ _
    (allFin-sound 16 (λ y → eqB (eqF (lookup (spL b) y) p) (eqF y p)) h x)) g)

-- Vectors of booleans, compared.
eqV : ∀ {n} → Vec Bool n → Vec Bool n → Bool
eqV {n} u v = allFin n (λ i → eqB (lookup u i) (lookup v i))
