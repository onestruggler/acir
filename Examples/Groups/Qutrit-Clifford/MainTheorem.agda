------------------------------------------------------------------------
-- Presentations of groups
--
-- Li, Mosca, Ross, van de Wetering and Zhao (2025): the main theorem,
-- for MainTheorems
--
-- The gates −ω, H, S, CZ and the rules C1–C18 of Figure 1 present the
-- n-qutrit Clifford group — the values the circuits denote, exact
-- scaled matrices over ℤ[ζ₁₂] — at every width (Presentation), and that
-- group has order 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ − 1) 9ᵏ (Count, Order).  This module
-- collects what MainTheorems states, behind one import: the circuits,
-- the rules at each width (_CRel,_===_), the group and its order, a
-- circuit's value ⟦_⟧ and their exact equality _≈ˢ_, derivability
-- ⊢_≈_, the presentation, and its completeness and soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.MainTheorem where

open import Algebra.Bundles using (Group)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Function.Bundles using (Inverse)
import Relation.Binary.PropositionalEquality as Eq

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.Qutrit-Clifford.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.Qutrit-Clifford.Presentation public using (Clifford)
open import Examples.Groups.Qutrit-Clifford.Count public using (order)
open import Examples.Groups.Qutrit-Clifford.Semantics public using (Sc)
import Examples.Groups.Qutrit-Clifford.CompletenessN as CN
import Examples.Groups.Qutrit-Clifford.Presentation as P
import Examples.Groups.Qutrit-Clifford.Semantics as Sem
import Examples.Groups.Qutrit-Clifford.Soundness as S

-- Equality by the rules.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

-- Exact equality of values.
infix 4 _≈ˢ_
_≈ˢ_ : ∀ {n} → Sc n → Sc n → Set
_≈ˢ_ = Sem._≈_

------------------------------------------------------------------------
-- The theorem

presentation : ∀ n → (n CRel,_===_) IsPresentationOf Clifford n
presentation = P.presentationᴳ

clifford-order : ∀ n → Inverse (Group.setoid (Clifford n)) (Eq.setoid (Fin (order n)))
clifford-order = P.clifford-group-order

-- A circuit's value: an exact scaled matrix over ℤ[ζ₁₂].
⟦_⟧ : ∀ {n} → Circuit n → Sc n
⟦_⟧ = Sem.⟦_⟧

complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ˢ ⟦ v ⟧ → ⊢ w ≈ v
complete {n} = CN.complete n

sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
sound = S.sound
