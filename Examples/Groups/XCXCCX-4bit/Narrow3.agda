------------------------------------------------------------------------
-- Presentations of groups
--
-- Three-wire steps in derivations on more wires
--
-- Completeness on three wires (Width3.complete₃), used in two ways.
-- by3 l r is Narrow2.by2 one wire wider: two letter lists on three
-- wires with the same function (decided, `same 3 ⟪ l ⟫ ⟪ r ⟫ ≡ true`
-- by refl) give an equation of the proof engine on the bottom three
-- wires of a circuit of any width (Circuit.Prop's pad₃), which lift⁼
-- moves up.  And Placed.Narrow at it: two words of placed letters on
-- any three of the four wires with the same function are equal
-- (narrow, narrowᵖ, narrow-low), which PlacedEngine's narrow steps use.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Narrow3 where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₃₊)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (same ; same-sound)
open import Examples.Groups.XCXCCX-4bit.Kit using (Eqn ; eqn ; ⟪_⟫)
open import Examples.Groups.XCXCCX-4bit.Narrow2 using (⟪map⟫)
open import Examples.Groups.XCXCCX-4bit.Width3 using (complete₃)
import Examples.Groups.XCXCCX-4bit.Placed as Placed

private
  variable
    n : ℕ

-- Two three-wire letter lists with the same function, on the bottom
-- three wires of any circuit.
by3 : (l r : List (Gen 3)) → same 3 ⟪ l ⟫ ⟪ r ⟫ ≡ true → Eqn (₃₊ n)
by3 {n} l r h = eqn (map (_↧ᵏ n) l) (map (_↧ᵏ n) r)
  (Eq.subst₂ ((₃₊ n) ⊢_≈_) (Eq.sym (⟪map⟫ (_↧ᵏ n) l)) (Eq.sym (⟪map⟫ (_↧ᵏ n) r))
     (pad₃ (complete₃ (same-sound ⟪ l ⟫ ⟪ r ⟫ h)) n))

private
  -- The Toffoli is an involution, on the bottom wires of four.
  test : Eqn 4
  test = by3 (gate₃ ⌈ CCX-gate ⌉ ∷ gate₃ ⌈ CCX-gate ⌉ ∷ []) [] Eq.refl

-- Placed letters on three of the four wires.
open Placed.Narrow complete₃ public
