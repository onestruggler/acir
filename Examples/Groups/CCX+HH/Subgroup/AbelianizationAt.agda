------------------------------------------------------------------------
-- Presentations of groups
--
-- Dimension-independent interface to the four-class abelianization.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Subgroup.AbelianizationAt where

open import Data.Nat.Base using (ℕ ; suc ; _≤_ ; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (Word ; ε)
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
open import Examples.Groups.CCX+HH.Subgroup.Action using (c00)
open import Examples.Groups.CCX+HH.Subgroup.Charge using (state)
import Examples.Groups.CCX+HH.Subgroup.AbelianizationCore as Core
import Examples.Groups.CCX+HH.Subgroup.Abelianization as Two

completeness : ∀ N → 2 ≤ N → {u v : Word (U.Gen N)} →
  state c00 u ≡ state c00 v → PB._≈_ (Core.Relations N) u v
completeness 0 ()
completeness 1 (s≤s ())
completeness (suc (suc N)) enough = Two.completeness N

kernel : ∀ N → 2 ≤ N → {w : Word (U.Gen N)} → state c00 w ≡ c00 → Core.Derived N w
kernel N enough {w} = completeness N enough {u = w} {v = ε}

kernel-only : ∀ N {w} → Core.Derived N w → state c00 w ≡ c00
kernel-only N = Core.soundness N
