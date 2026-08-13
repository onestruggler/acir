------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing a CZ past an L' box (two wires).
--
-- The statement is a case split on L' 2 ⊎ L' 1, so it is proved one
-- component at a time -- L2-CZ.Left for the L' 2 boxes, L2-CZ.Right
-- for the L' 1 ones -- and combined here by dispatch.  The four names
-- consumers use (intp, l'-of, dir-of, lemma-dir-and-l') keep their
-- meanings, and l'-of / dir-of still compute on a concrete box, since
-- each branch just forwards to the component's clauses.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --call-by-name --termination-depth=4 #-}


open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _≟_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty using (⊥-elim)

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations



open import Presentation.GroupLike
open import Data.Nat.Primality




module Examples.Groups.Symplectic.BR.Two.L2-CZ (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Examples.Groups.Symplectic.BR.Two.L2-CZ.Base  p-2 p-prime public
open import Examples.Groups.Symplectic.BR.Two.L2-CZ.Left  p-2 p-prime
open import Examples.Groups.Symplectic.BR.Two.L2-CZ.Right p-2 p-prime

l'-of : L' 2 ⊎ L' 1 → L' 2 ⊎ L' 1
l'-of (inj₁ l) = l'-of₁ l
l'-of (inj₂ r) = l'-of₂ r

dir-of : L' 2 ⊎ L' 1 → Word (Gen 2)
dir-of (inj₁ l) = dir-of₁ l
dir-of (inj₂ r) = dir-of₂ r

lemma-dir-and-l' : ∀ (l : L' 2 ⊎ L' 1) →
  let
  dir = dir-of l
  l' = l'-of l
  in

  intp l • CZ ≈ dir • intp l'
lemma-dir-and-l' (inj₁ l) = lemma₁ l
lemma-dir-and-l' (inj₂ r) = lemma₂ r
