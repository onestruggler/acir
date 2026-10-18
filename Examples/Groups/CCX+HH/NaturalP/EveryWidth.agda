------------------------------------------------------------------------
-- Presentations of groups
--
-- From twelve wires to every width.
--
-- If the rules with the schema are complete on at most twelve wires,
-- they are complete at every width (`every-width`): on 12 + k wires
-- this is WidthComplete with c = 8, whose hypotheses are completeness
-- on at most eight wires and on twelve.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.EveryWidth where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _≤_ ; z≤n ; s≤s)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; subst)
open import Relation.Nullary using (yes ; no)
open import Notations using (₄₊)

import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S
import Examples.Groups.CCX+HH.NaturalP.WidthComplete as WC

-- The rules with the schema are complete on n wires.
Complete : ℕ → Set
Complete n = ∀ {u v : P.Circuit n} → interpret u ≡ interpret v → n S.⊢ u ≈ v

private
  8≤12 : 8 ≤ 12
  8≤12 = NP.m≤m+n 8 4

  -- 12 + k wires, as WidthComplete writes them.
  width : ∀ k → ₄₊ (k + (8 + 0)) ≡ k + 12
  width k = trans (cong (λ m → ₄₊ (k + m)) (NP.+-identityʳ 8))
    (trans (NP.+-comm 4 (k + 8)) (NP.+-assoc k 8 4))

every-width : (∀ {n} → n ≤ 12 → Complete n) → ∀ n → Complete n
every-width h n with n NP.≤? 12
... | yes le = h le
... | no gt  = subst Complete eq (WC.complete (λ le → h (NP.≤-trans le 8≤12)) k 8 NP.≤-refl (h NP.≤-refl))
  where
  k = n ∸ 12
  eq : ₄₊ (k + (8 + 0)) ≡ n
  eq = trans (width k) (NP.m∸n+n≡m (NP.<⇒≤ (NP.≰⇒> gt)))
