------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits under several controls.
--
-- A control pattern assigns to each of the bottom wires either a
-- control of one colour (true: the wire must be 1, false: it must be 0)
-- or an idle wire.  Λ s w is w on the wires above them, under the
-- pattern s (wire 0 is the first position): ctrl, ctrl⁻ or _↑ for each.
-- σat s₁ is the swap of the two positions after s₁, and Xat s₁ the X
-- on the position after s₁.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Lambda where

open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; _+_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Notations using (₁₊ ; ₂₊ ; ₄₊)

open import Examples.Groups.CCX+HH.NaturalP.Schema using (Circuit ; _↑ ; σ ; X)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl ; ctrl⁻)

private
  variable
    m i k c : ℕ

-- A position of a pattern.
Pos : Set
Pos = Maybe Bool

ctrlᵖ : Pos → Circuit m → Circuit (₁₊ m)
ctrlᵖ (just true)  = ctrl
ctrlᵖ (just false) = ctrl⁻
ctrlᵖ nothing      = _↑

-- w under the pattern s.
Λ : Vec Pos k → Circuit (₄₊ c) → Circuit (₄₊ (k + c))
Λ []      w = w
Λ (p ∷ s) w = ctrlᵖ p (Λ s w)

-- The swap of the positions i and i + 1 of a pattern of length i + 2 + j.
σat : Vec Pos i → (j c : ℕ) → Circuit (₄₊ ((i + ₂₊ j) + c))
σat []      j c = σ
σat (p ∷ s) j c = σat s j c ↑

-- The X of the position i of a pattern of length i + 1 + j.
Xat : Vec Pos i → (j c : ℕ) → Circuit (₄₊ ((i + ₁₊ j) + c))
Xat []      j c = X
Xat (p ∷ s) j c = Xat s j c ↑

-- The colour of a position exchanged.
flip : Pos → Pos
flip (just b) = just (not b)
flip nothing  = nothing
