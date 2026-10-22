------------------------------------------------------------------------
-- Presentations of groups
--
-- The swap rules that the placements use, as a record
--
-- TopWeakening, Place and Windows carry circuits across wires with the
-- cycles of swaps, and need of the swap only that it is an involution
-- and passes a one- or two-wire gate to the other wires.  Swaps proves
-- these by completeness on two and three wires (`Swaps.facts`); stated
-- here, the laws that use them take them as an argument, so that the
-- window libraries, which take them too, need not wait for that proof.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.SwapFacts where

open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Clifford+CS.Syntactics

record SwapFacts : Set where
  field
    Swap² : ∀ {n} → (₂₊ n) ⊢ Swap • Swap ≈ ε
    swap₁ : ∀ {n} (h : Gate 1) → (₂₊ n) ⊢ [ gate₁ h ]ʷ ↑ • Swap ≈ Swap • [ gate₁ h ]ʷ
    swap₂ : ∀ {n} (h : Gate 2) →
            (₃₊ n) ⊢ [ gate₂ h ]ʷ ↑ • Swap • Swap ↑ ≈ Swap • Swap ↑ • [ gate₂ h ]ʷ
