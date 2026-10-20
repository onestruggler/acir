------------------------------------------------------------------------
-- Presentations of groups
--
-- Letter lists written as strings, for the generated derivations
--
-- The box relations' derivations (Box2, Box3) are long lists of
-- letters.  Written out as h₀ ∷ c₀ ∷ …, they cost Agda most of its
-- time in operator parsing, an implicit width to solve per letter, and
-- large interfaces; ℓ "HC…" is one token, decoded by evaluation.  One
-- character per letter: H, I, J are H on the wires 0, 1, 2; S, T, U
-- likewise S; C and D are CZ on the wires 0 1 and 1 2; n is the scalar
-- −ω.  ℓ is polymorphic in the width, which unification reads off the
-- expected type, and decodes a letter as soon as the width shows
-- enough wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Letters where

open import Data.Char.Base using (Char)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.String.Base using (String ; toList)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations using (₁₊)
open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine
  using (Eqn ; Step ; perm ; rw ; run ; derive ; sym⁼ ; lift⁼)

private
  data Kind : Set where
    kH kS kC : Kind

  -- A gate of the given kind on wire w of a circuit on m wires.
  place : (m w : ℕ) → Kind → Maybe (Gen m)
  place (suc m)       zero    kH = just (gate₁ H-gate)
  place (suc m)       zero    kS = just (gate₁ S-gate)
  place (suc (suc m)) zero    kC = just (gate₂ CZ-gate)
  place (suc m)       (suc w) k  = up (place m w k)
    where
    up : Maybe (Gen m) → Maybe (Gen (suc m))
    up (just g) = just (g ↥)
    up nothing  = nothing
  place _             _       _  = nothing

  letter : (m : ℕ) → Char → Maybe (Gen m)
  letter m 'H' = place m 0 kH
  letter m 'I' = place m 1 kH
  letter m 'J' = place m 2 kH
  letter m 'S' = place m 0 kS
  letter m 'T' = place m 1 kS
  letter m 'U' = place m 2 kS
  letter m 'C' = place m 0 kC
  letter m 'D' = place m 1 kC
  letter m 'n' = just (gate₀ ν-gate)
  letter m _   = nothing

  decode : (m : ℕ) → List Char → List (Gen m)
  decode m []       = []
  decode m (c ∷ cs) = add (letter m c) (decode m cs)
    where
    add : Maybe (Gen m) → List (Gen m) → List (Gen m)
    add (just g) xs = g ∷ xs
    add nothing  xs = xs

ℓ : ∀ {m} → String → List (Gen m)
ℓ {m} s = decode m (toList s)

------------------------------------------------------------------------
-- Steps without parentheses
--
-- Agda's operator parser takes time in proportion to the names in
-- scope for every parenthesised subterm, and the derivations have
-- thousands of steps with thousands of lemmas in scope: rw 3 (sym⁼ e)
-- is written rwˢ 3 e.

private
  variable
    n : ℕ

rwˢ : ℕ → Eqn n → Step n
rwˢ i e = rw i (sym⁼ e)

rwˡ : ℕ → Eqn n → Step (₁₊ n)
rwˡ i e = rw i (lift⁼ e)

rwˢˡ : ℕ → Eqn n → Step (₁₊ n)
rwˢˡ i e = rw i (sym⁼ (lift⁼ e))

permℓ : String → Step n
permℓ s = perm (ℓ s)

deriveℓ : (l r : String) (ss : List (Step n)) → run ss (ℓ l) ≡ just (ℓ r) → Eqn n
deriveℓ l r = derive (ℓ l) (ℓ r)
