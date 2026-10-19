------------------------------------------------------------------------
-- Presentations of groups
--
-- Refuting an impossible order of two indices, for the dispatch modules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.ThreeWire.DispKit where

open import Data.Bool.Base using (T)
open import Data.Fin.Base using (Fin ; toℕ ; _<_)
open import Data.Nat.Base as ℕ using (_≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤ ; <⇒≱)
open import Relation.Nullary using (¬_)

refute< : ∀ {a b : Fin 8} → T (toℕ b ℕ.≤ᵇ toℕ a) → ¬ (a < b)
refute< {a} {b} h p = <⇒≱ p (≤ᵇ⇒≤ (toℕ b) (toℕ a) h)
