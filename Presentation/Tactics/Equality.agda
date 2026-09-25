------------------------------------------------------------------------
-- Presentations of groups
--
-- Propositional equality, with the equational syntax of the Bian–
-- Selinger Agda code (CC BY 2.0): imported qualified, as Eq,
--
--   Eq.equational a₀
--       Eq.by reason₁
--      equals a₁
--          …
--
-- next to the judgemental syntax of Presentation.Tactics.Judgement.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Presentation.Tactics.Equality where

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

infix 2 equational_
infixl 1 by-equals
infixl 4 _reversed

equational_ : ∀ {A : Set} (a : A) → a ≡ a
equational_ a = refl

by-equals : ∀ {A : Set} {a b : A} → a ≡ b → (c : A) → b ≡ c → a ≡ c
by-equals eq c reason = trans eq reason

syntax by-equals eq c reason = eq by reason equals c

_reversed : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
_reversed = sym

definition : ∀ {A : Set} {a : A} → a ≡ a
definition = refl

auto : ∀ {A : Set} {a : A} → a ≡ a
auto = refl
