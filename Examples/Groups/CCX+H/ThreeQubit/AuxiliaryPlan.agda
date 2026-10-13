------------------------------------------------------------------------
-- Presentations of groups
--
-- Read the decoder's intermediate atoms in the auxiliary alphabet.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.ThreeQubit.AuxiliaryPlan where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (yes ; no ; recompute)
open import Data.Empty using (⊥-elim)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
open import Word.Base using (Word ; [_]ʷ ; ε ; _ʷ)
open import Examples.Groups.CCX+H.ThreeQubit.Decoding using (Atom ; sign ; exchange ; k0 ; ih)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T

xword : Fin 8 → Fin 8 → Word (T.Genᴸ 8)
xword a b with a FP.<? b
... | yes p = T.Xᴸ a b p
... | no _ with b FP.<? a
...   | yes p = T.Xᴸ b a p
...   | no _ = ε

xword-ordered : ∀ a b .(p : a < b) → xword a b ≡ T.Xᴸ a b p
xword-ordered a b p with a FP.<? b
... | yes _ = refl
... | no not-less = ⊥-elim (not-less (recompute (a FP.<? b) p))

aux : Atom → Word (T.Genᴸ 8)
aux (sign a) = T.Mᴸ a
aux (exchange a b) = xword a b
aux k0 = T.Kᴸ ₀ ₁ ₂ ₃ (s≤s z≤n) (s≤s (s≤s z≤n))
                            (s≤s (s≤s (s≤s z≤n)))
aux ih = T.H
