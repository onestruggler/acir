------------------------------------------------------------------------
-- Presentations of groups
--
-- The abelianization of the physical HH circuit group at every width:
--   zero wires: trivial; one wire: C2; two wires: C2 x C2;
--   three wires: C2; four or more wires: trivial (the group is perfect).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.AbelianizationClassification where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
import Algebra.Construct.Terminal as Terminal
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)
open import Word.Base using (ε)
import Presentation.Base as PB
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Abelianization as Abel
import Examples.Groups.CCX+HH.LowWidth.AbelianTools as Tools
import Examples.Groups.CCX+HH.LowWidthAbelianization as Low
import Examples.Groups.CCX+HH.GeneralN.Perfect as Perfect
open Tools public using (abelian-group)

model : ℕ → Group 0ℓ 0ℓ
model 0 = Terminal.group
model 1 = Tools.C₂
model 2 = Tools.C₂×C₂
model 3 = Tools.C₂
model (suc (suc (suc (suc n)))) = Terminal.group

character : ∀ n → H.Circuit n → Group.Carrier (model n)
character 0 w = tt
character 1 = Low.One.character
character 2 = Low.Two.character
character 3 = Low.Three.character
character (suc (suc (suc (suc n)))) w = tt

private
  trivial-isomorphism : ∀ n →
    (∀ (w : H.Circuit n) → Abel.At._≈_ n w ε) →
    GroupMorphisms.IsGroupIsomorphism
      (Group.rawGroup (abelian-group n)) (Group.rawGroup Terminal.group) (λ _ → tt)
  trivial-isomorphism n vanish = Tools.Bundle.build n Terminal.group (λ _ → tt)
    (λ _ → tt) (λ {u} {v} _ → PB.trans (vanish u) (PB.sym (vanish v)))
    (λ _ _ → tt) tt (λ _ → ε) (λ _ → tt)

isomorphism : ∀ n → GroupMorphisms.IsGroupIsomorphism
  (Group.rawGroup (abelian-group n)) (Group.rawGroup (model n)) (character n)
isomorphism 0 = trivial-isomorphism 0 Low.Zero.trivial
isomorphism 1 = Low.One.isomorphism
isomorphism 2 = Low.Two.isomorphism
isomorphism 3 = Low.Three.isomorphism
isomorphism (suc (suc (suc (suc n)))) =
  trivial-isomorphism (suc (suc (suc (suc n)))) (Perfect.abelian-trivial n)
