------------------------------------------------------------------------
-- Presentations of groups
--
-- The invariant that separates the cosets of a colouring's stabiliser.
--
-- ψ g records the colour of the level g sends each level to.  A letter
-- b that preserves the colouring (`keeps b`, decided) leaves ψ
-- unchanged on the left (`ψ-mul`): b • g sends x to a level of the same
-- colour as g does.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (Fin)

module Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.StabCol
  (col : Fin 16 → Fin 16) where

open import Data.Bool.Base using (Bool)
open import Data.Vec.Base using (Vec ; map ; lookup)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound ; eqF ; eqF-sound)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Gamma using (L ; P ; spL ; mul)

ψ : P → Vec (Fin 16) 16
ψ g = map col g

keeps : L → Bool
keeps b = allFin 16 (λ x → eqF (col (lookup (spL b) x)) (col x))

ψ-mul : ∀ b → keeps b ≡ true → ∀ g → ψ (mul (spL b) g) ≡ ψ g
ψ-mul b h g = Eq.trans (Eq.sym (VP.map-∘ col (lookup (spL b)) g))
  (VP.map-cong (λ x → eqF-sound _ _
    (allFin-sound 16 (λ y → eqF (col (lookup (spL b) y)) (col y)) h x)) g)

-- Colourings, compared.
eqC : Vec (Fin 16) 16 → Vec (Fin 16) 16 → Bool
eqC u v = allFin 16 (λ i → eqF (lookup u i) (lookup v i))
