------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical physical circuit normal forms at every wire count.
-- Normal forms are actual circuits, with literal equality as their
-- comparison.  No shortest-word or computational efficiency claim is
-- made for this construction.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Normalization where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as C
import Examples.Groups.CCX+H.LowWidthNormalization as Low
import Examples.Groups.CCX+H.GeneralN.Normalization as General

nf : ∀ {n} → H.Circuit n → H.Circuit n
nf {0} = Low.Zero.nf
nf {1} = Low.One.nf
nf {2} = Low.Two.nf
nf {3} = Low.Three.nf
nf {suc (suc (suc (suc n)))} = General.nf n

correct : ∀ {n} (w : H.Circuit n) → C.interpret (nf w) ≡ C.interpret w
correct {0} = Low.Zero.correct
correct {1} = Low.One.correct
correct {2} = Low.Two.correct
correct {3} = Low.Three.correct
correct {suc (suc (suc (suc n)))} = General.correct n

semantic-cong : ∀ {n} {u v : H.Circuit n} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
semantic-cong {0} {u} {v} = Low.Zero.semantic-cong {u} {v}
semantic-cong {1} {u} {v} = Low.One.semantic-cong {u} {v}
semantic-cong {2} {u} {v} = Low.Two.semantic-cong {u} {v}
semantic-cong {3} {u} {v} = Low.Three.semantic-cong {u} {v}
semantic-cong {suc (suc (suc (suc n)))} {u} {v} = General.semantic-cong n {u} {v}

normalize : ∀ {n} (w : H.Circuit n) → n P.⊢ w ≈ nf w
normalize {n} w = P.complete n {u = w} {v = nf w} (Eq.sym (correct w))

cong : ∀ {n} {u v : H.Circuit n} → n P.⊢ u ≈ v → nf u ≡ nf v
cong {n} {u} {v} eq = semantic-cong {u = u} {v = v} (P.sound n eq)

complete : ∀ {n} {u v : H.Circuit n} → nf u ≡ nf v → n P.⊢ u ≈ v
complete {n} {u} {v} eq = P.complete n {u = u} {v = v}
  (Eq.trans (Eq.sym (correct u)) (Eq.trans (Eq.cong C.interpret eq) (correct v)))

idempotent : ∀ {n} (w : H.Circuit n) → nf (nf w) ≡ nf w
idempotent w = semantic-cong {u = nf w} {v = w} (correct w)
