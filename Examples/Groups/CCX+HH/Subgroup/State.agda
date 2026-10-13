------------------------------------------------------------------------
-- Presentations of groups
--
-- Right actions of a presented monoid on coset states.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

module Examples.Groups.CCX+HH.Subgroup.State
  {Y C : Set} (step : C → Y → C) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Presentation.Base as PB

state : C → Word Y → C
state c [ y ]ʷ = step c y
state c ε = c
state c (u • v) = state (state c u) v

module Congruence (Δ : WRel Y)
  (relations : ∀ c {u v} → Δ u v → state c u ≡ state c v) where

  state-cong : ∀ c {u v} → PB._≈_ Δ u v → state c u ≡ state c v
  state-cong c PB.refl = Eq.refl
  state-cong c (PB.sym p) = Eq.sym (state-cong c p)
  state-cong c (PB.trans p q) = Eq.trans (state-cong c p) (state-cong c q)
  state-cong c (PB.cong {w' = u′} {v = v} p q) =
    Eq.trans (Eq.cong (λ d → state d v) (state-cong c p))
             (state-cong (state c u′) q)
  state-cong c PB.assoc = Eq.refl
  state-cong c PB.left-unit = Eq.refl
  state-cong c PB.right-unit = Eq.refl
  state-cong c (PB.axiom ax) = relations c ax
