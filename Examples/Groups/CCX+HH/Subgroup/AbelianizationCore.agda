------------------------------------------------------------------------
-- Presentations of groups
--
-- The universal commutative quotient of the dyadic presentation.
-- Its identity class is the commutator subgroup, by the definition of
-- abelianization.  This relation is used to characterize the physical
-- image; it is never an axiom of the physical circuit theory.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.Subgroup.AbelianizationCore (n : ℕ) where

open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Presentation.GroupLike as GL
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as D
open import Examples.Groups.CCX+HH.Subgroup.Action using (c00 ; dyadic-step)
import Examples.Groups.CCX+HH.Subgroup.Action as Action
import Examples.Groups.CCX+HH.Subgroup.State as State
import Examples.Groups.CCX+HH.Subgroup.Charge as Charge

private
  module Source = PB (U._===_ {n})
  module A = Action.At n

data Relations : WRel (U.Gen n) where
  source : ∀ {u v} → U._===_ u v → Relations u v
  commute : ∀ u v → Relations (u • v) (v • u)

open PB Relations public hiding (_===_)
open import Presentation.Properties Relations using (by-assoc ; word-setoid)
open import Relation.Binary.Reasoning.Setoid word-setoid

source-cong : ∀ {u v} → u Source.≈ v → u ≈ v
source-cong PB.refl = refl
source-cong (PB.sym p) = sym (source-cong p)
source-cong (PB.trans p q) = trans (source-cong p) (source-cong q)
source-cong (PB.cong p q) = cong (source-cong p) (source-cong q)
source-cong PB.assoc = assoc
source-cong PB.left-unit = left-unit
source-cong PB.right-unit = right-unit
source-cong (PB.axiom p) = axiom (source p)

grouplike : GL.Grouplike Relations
grouplike g = [ g ]ʷ , source-cong (D.gen-gen g)

private
  module G = GL.Group-Lemmas Relations grouplike
  action-relations : ∀ c {u v} → Relations u v → A.state c u ≡ A.state c v
  action-relations c (source ax) = A.state-relations c ax
  action-relations c (commute u v) = Charge.word-commute c u v
  module Model = State.Congruence dyadic-step Relations action-relations

soundness : ∀ {u v} → u ≈ v → A.state c00 u ≡ A.state c00 v
soundness = Model.state-cong c00

commutator : Word (U.Gen n) → Word (U.Gen n) → Word (U.Gen n)
commutator u v = ((u • v) • D._⁻¹ u) • D._⁻¹ v

commutator-trivial : ∀ u v → commutator u v ≈ ε
commutator-trivial u v = begin
  ((u • v) • D._⁻¹ u) • D._⁻¹ v ≈⟨ cong assoc refl ⟩
  (u • (v • D._⁻¹ u)) • D._⁻¹ v
    ≈⟨ cong (cong refl (axiom (commute v (D._⁻¹ u)))) refl ⟩
  (u • (D._⁻¹ u • v)) • D._⁻¹ v ≈⟨ trans (cong (sym assoc) refl) assoc ⟩
  (u • D._⁻¹ u) • (v • D._⁻¹ v)
    ≈⟨ cong (source-cong (D.inverseʳ {g = u})) (source-cong (D.inverseʳ {g = v})) ⟩
  ε • ε ≈⟨ left-unit ⟩
  ε ∎

Derived : Word (U.Gen n) → Set
Derived w = w ≈ ε

commutator-member : ∀ u v → Derived (commutator u v)
commutator-member = commutator-trivial

derived-product : ∀ {u v} → Derived u → Derived v → Derived (u • v)
derived-product p q = trans (cong p q) left-unit

derived-inverse : ∀ {w} → Derived w → Derived (D._⁻¹ w)
derived-inverse {w} p = trans (sym right-unit)
  (trans (cong refl (sym p)) (source-cong (D.inverseˡ {g = w})))

derived-conjugate : ∀ u {v} → Derived v → Derived ((u • v) • D._⁻¹ u)
derived-conjugate u p = trans (cong (cong refl p) refl)
  (trans (cong right-unit refl) (source-cong (D.inverseʳ {g = u})))

-- Every interpretation of Table 1 in a commutative presented monoid
-- factors through this quotient.  No target-specific semantic equation
-- has been built into Relations.
module Universal {Y : Set} (Δ : WRel Y) (f : U.Gen n → Word Y)
  (source-respects : ∀ {u v} → U._===_ u v →
    PB._≈_ Δ ((f ʷ) u) ((f ʷ) v))
  (commutative : ∀ u v → PB._≈_ Δ (u • v) (v • u)) where

  private
    relations-respect : ∀ {u v} → Relations u v →
      PB._≈_ Δ ((f ʷ) u) ((f ʷ) v)
    relations-respect (source ax) = source-respects ax
    relations-respect (commute u v) = commutative ((f ʷ) u) ((f ʷ) v)

  factor-respects : ∀ {u v} → u ≈ v → PB._≈_ Δ ((f ʷ) u) ((f ʷ) v)
  factor-respects = PP.StarCongruence.fʷ-cong Relations Δ f relations-respect
