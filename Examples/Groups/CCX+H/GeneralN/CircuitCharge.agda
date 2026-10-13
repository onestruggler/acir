------------------------------------------------------------------------
-- Presentations of groups
--
-- Every structurally encoded CCX+H circuit on at least four wires lies
-- in the four-state stabilizer.  The dyadic part fixes every state;
-- the last IH in an encoded Hadamard fixes the distinguished state 00.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.CircuitCharge where

open import Data.Nat.Base using (ℕ ; _+_) renaming (_^_ to _^ℕ_)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.GeneralN.StructuralEncoding as E
import Examples.Groups.CCX+H.GeneralN.Action as A
import Examples.Groups.CCX+HH.Syntactics as D
import Examples.Groups.CCX+HH.StructuralEncoding as DE
import Examples.Groups.CCX+HH.Subgroup.CircuitCharge as DC
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T

open A using (c00)

module At (n : ℕ) where
  open A.At (2 ^ℕ (4 + n)) using (state ; state-lift)

  dyadic-closed : ∀ (w : D.Circuit (4 + n)) →
    state c00 T.⌊ DE.encode w ⌋ʷ ≡ c00
  dyadic-closed w = Eq.trans (state-lift c00 (DE.encode w))
    (DC.image-closed c00 w)

  gen-closed : ∀ (g : Gen (4 + n)) → state c00 (E.e g) ≡ c00
  gen-closed g with E.classify g
  ... | inj₁ dg = Eq.trans (state-lift c00 (DE.e dg)) (DC.gen-closed c00 dg)
  ... | inj₂ p = Eq.cong A.shear (dyadic-closed (E.prefix p))

  image-closed : ∀ (w : Circuit (4 + n)) → state c00 (E.encode w) ≡ c00
  image-closed [ g ]ʷ = gen-closed g
  image-closed ε = Eq.refl
  image-closed (u • v) =
    Eq.trans (Eq.cong (λ c → state c (E.encode v)) (image-closed u))
      (image-closed v)
