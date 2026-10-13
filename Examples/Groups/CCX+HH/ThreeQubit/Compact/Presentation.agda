------------------------------------------------------------------------
-- Presentations of groups
--
-- The 105 compact stabilizer equations are complete for their Table 1
-- denotations, by deriving every step of the finite normal-form table.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Compact.Presentation where

open import Word.Base using (_ʷ)
open import Examples.Groups.CCX+HH.ThreeQubit.Compact.Syntactics public
  using (_===_ ; _≈_ ; phase-square ; phase-commute ; symmetric ; cross)
open import Examples.Groups.CCX+HH.ThreeQubit.Compact.Soundness public
  using (encode-axiom ; encode-cong)
import Examples.Groups.CCX+HH.ThreeQubit.Compact.Normalization as N
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerPresentation as Base
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (b)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Presentation.Base as PB

private
  module B = PB Base._===_
  module R = PB _===_

derive-axiom : ∀ {u v} → Base._===_ u v → u ≈ v
derive-axiom Base.start = N.initial
derive-axiom (Base.table g n) = N.factor g n

derive : ∀ {u v} → u B.≈ v → u ≈ v
derive B.refl = R.refl
derive (B.sym p) = R.sym (derive p)
derive (B.trans p q) = R.trans (derive p) (derive q)
derive (B.cong p q) = R.cong (derive p) (derive q)
derive B.assoc = R.assoc
derive B.left-unit = R.left-unit
derive B.right-unit = R.right-unit
derive (B.axiom p) = derive-axiom p

encode-injective : ∀ {u v} → PB._≈_ (T._===_ {8}) ((b ʷ) u) ((b ʷ) v) → u ≈ v
encode-injective eq = derive (Base.encode-injective eq)
