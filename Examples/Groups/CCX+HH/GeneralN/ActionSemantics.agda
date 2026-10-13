------------------------------------------------------------------------
-- Presentations of groups
--
-- Equality of physical matrices is exactly equality of their actions
-- on all state vectors.  This bridge does not use circuit completeness.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.ActionSemantics where

open import Relation.Binary.PropositionalEquality
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
  using (quantum ; quantum-column ; encoding-action)

action⇒matrix : ∀ {n} {u v : Circuit n} →
  (∀ x → quantum u x ≡ quantum v x) → Q.interpret u ≡ Q.interpret v
action⇒matrix {u = u} {v} eq = A.col-ext λ i → trans (quantum-column u i)
  (trans (eq _) (sym (quantum-column v i)))

matrix⇒action : ∀ {n} {u v : Circuit n} → Q.interpret u ≡ Q.interpret v →
  ∀ x → quantum u x ≡ quantum v x
matrix⇒action {u = u} {v} eq x = trans (sym (encoding-action u x))
  (trans (A.same-action (E.encode u) (E.encode v)
    (trans (Q.encoding-correct u) (trans eq (sym (Q.encoding-correct v)))) x)
    (encoding-action v x))
