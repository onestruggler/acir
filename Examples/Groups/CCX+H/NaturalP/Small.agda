------------------------------------------------------------------------
-- Presentations of groups
--
-- The CCX+H rules with the swap gate are complete on at most two wires,
-- and so at every width but three given CCX+HH's on at most twelve.
--
-- On no wires every circuit is ε; on one and two wires completeness is
-- Natural's (Natural/Width1, Natural/Width2), carried over by Bridge.
-- With Complete.every-width, completeness at every width then needs
-- only completeness of CCX+HH.NaturalP with the schema on at most twelve
-- wires and of these rules on three (`every-width`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Small where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.CCX+H.NaturalP.Complete as C using (Complete)
open import Examples.Groups.CCX+H.NaturalP.Bridge using (complete⇒ ; complete₀)
import Examples.Groups.CCX+H.Natural.Width1 as W1
import Examples.Groups.CCX+H.Natural.Width2 as W2
import Examples.Groups.CCX+HH.NaturalP.EveryWidth as PE

complete₁ : Complete 1
complete₁ = complete⇒ W1.complete

complete₂ : Complete 2
complete₂ = complete⇒ W2.complete

-- Every width, given CCX+HH's rules on at most twelve wires and these
-- on three.
every-width : (∀ {n} → n ≤ 12 → PE.Complete n) → Complete 3 → ∀ n → Complete n
every-width h c₃ = C.every-width h low
  where
  low : ∀ {n} → n ≤ 3 → Complete n
  low {zero}  _ = complete₀
  low {suc zero} _ = complete₁
  low {suc (suc zero)} _ = complete₂
  low {suc (suc (suc zero))} _ = c₃
  low {suc (suc (suc (suc n)))} (s≤s (s≤s (s≤s ())))
