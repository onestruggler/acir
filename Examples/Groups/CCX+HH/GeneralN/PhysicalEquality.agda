------------------------------------------------------------------------
-- Presentations of groups
--
-- Matrix equality and action equality for a physical circuit compared
-- with its two-level decoding target.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.PhysicalEquality where

open import Data.Nat.Base using (ℕ ; _^_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; _•_)
open import Quantum.Synthesis.Matrix using (_·*·_)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum ; encoding-action ; quantum-column)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis-col)

private variable n : ℕ

matrix⇒action : ∀ (w : H.Circuit n) (v : Word (T.Gen (2 ^ n))) →
  Q.interpret w ≡ A.⟦ v ⟧ᵐ → ∀ x → quantum w x ≡ A.actVʷ v x
matrix⇒action w v eq x = trans (sym (encoding-action w x))
  (A.same-action (E.encode w) v (trans (Q.encoding-correct w) eq) x)

action⇒matrix : ∀ (w : H.Circuit n) (v : Word (T.Gen (2 ^ n))) →
  (∀ x → quantum w x ≡ A.actVʷ v x) → Q.interpret w ≡ A.⟦ v ⟧ᵐ
action⇒matrix w v eq = A.col-ext λ i → trans (quantum-column w i)
  (trans (eq _) (sym (trans (A.col-actMʷ v A.𝕀 i)
    (cong (A.actVʷ v) (sym (basis-col i))))))

product : ∀ (u v : H.Circuit n) (a b : Word (T.Gen (2 ^ n))) →
  Q.interpret u ≡ A.⟦ a ⟧ᵐ → Q.interpret v ≡ A.⟦ b ⟧ᵐ →
  Q.interpret (u • v) ≡ A.⟦ a • b ⟧ᵐ
product u v a b eq eq′ = trans (cong₂ _·*·_ eq eq′) (sym (A.⟦•⟧ᵐ a b))
