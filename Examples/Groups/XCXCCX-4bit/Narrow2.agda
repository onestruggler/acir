------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-wire steps in derivations on more wires
--
-- by2 l r turns two letter lists on two wires with the same function
-- (decided: `same 2 ⟪ l ⟫ ⟪ r ⟫ ≡ true`, by refl) into an equation of
-- the proof engine on the bottom two wires of a circuit of any width:
-- completeness on two wires (Width2.complete₂), padded (Circuit.Prop's
-- pad₂).  lift⁼ moves it up, so any two-wire step on adjacent wires is
-- one rewrite.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Narrow2 where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₂₊)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (same ; same-sound)
open import Examples.Groups.XCXCCX-4bit.Kit
open import Examples.Groups.XCXCCX-4bit.Width2 using (complete₂)

private
  variable
    k m n : ℕ

-- A letter list mapped is the word mapped.
⟪map⟫ : (f : Gen m → Gen k) (xs : List (Gen m)) → ⟪ map f xs ⟫ ≡ wmap f ⟪ xs ⟫
⟪map⟫ f []       = refl
⟪map⟫ f (x ∷ xs) = Eq.cong ([ f x ]ʷ •_) (⟪map⟫ f xs)

-- Two two-wire letter lists with the same function, on the bottom two
-- wires of any circuit.
by2 : (l r : List (Gen 2)) → same 2 ⟪ l ⟫ ⟪ r ⟫ ≡ true → Eqn (₂₊ n)
by2 {n} l r h = eqn (map (_↧ᵏ n) l) (map (_↧ᵏ n) r)
  (Eq.subst₂ ((₂₊ n) ⊢_≈_) (Eq.sym (⟪map⟫ (_↧ᵏ n) l)) (Eq.sym (⟪map⟫ (_↧ᵏ n) r))
     (pad₂ (complete₂ (same-sound ⟪ l ⟫ ⟪ r ⟫ h)) n))
