------------------------------------------------------------------------
-- Presentations of groups
--
-- The swap rules: a gate passes the swap to the other wire
--
-- Clément's theory states these as its rules (f1)–(f4) of Remark 1;
-- here they are theorems, decided on two and three wires by
-- completeness there (SemanticSteps).  They are what the cycles of
-- TopWeakening and Place need, with the swap being an involution.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Swaps where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
import Examples.Groups.Clifford+CS.TwoQubit as TwoQubit
import Examples.Groups.Clifford+CS.TwoQubit.Decoding as Decoding
import Examples.Groups.Clifford+CS.ThreeQubit as ThreeQubit

private
  variable
    n : ℕ

  module S₂ = Below 2 (TwoQubit.Lemma-7-6.complete Decoding.lemma-7-4 Decoding.lemma-7-5)
  module S₃ = Below 3 ThreeQubit.complete

-- The swap is an involution.
Swap² : (₂₊ n) ⊢ Swap • Swap ≈ ε
Swap² = S₂.by-sem (Swap • Swap) ε Eq.refl

-- A one-wire gate passes the swap.
swap-S : (₂₊ n) ⊢ S ↑ • Swap ≈ Swap • S
swap-S = S₂.by-sem (S ↑ • Swap) (Swap • S) Eq.refl

swap-K : (₂₊ n) ⊢ K ↑ • Swap ≈ Swap • K
swap-K = S₂.by-sem (K ↑ • Swap) (Swap • K) Eq.refl

-- So does X, in both directions.
swap-X : (₂₊ n) ⊢ X ↑ • Swap ≈ Swap • X
swap-X = S₂.by-sem (X ↑ • Swap) (Swap • X) Eq.refl

swap-X′ : (₂₊ n) ⊢ Swap • X ↑ ≈ X • Swap
swap-X′ = S₂.by-sem (Swap • X ↑) (X • Swap) Eq.refl

-- CS on wires 1, 2 passes the two swaps that carry wire 0 to wire 2.
swap-CS : (₃₊ n) ⊢ CS ↑ • Swap • Swap ↑ ≈ Swap • Swap ↑ • CS
swap-CS = S₃.by-sem (CS ↑ • Swap • Swap ↑) (Swap • Swap ↑ • CS) Eq.refl

-- The one-wire gates, and the two-wire gate, by cases.
swap₁ : ∀ (h : Gate 1) → (₂₊ n) ⊢ [ gate₁ h ]ʷ ↑ • Swap ≈ Swap • [ gate₁ h ]ʷ
swap₁ S-gate = swap-S
swap₁ K-gate = swap-K

swap₂ : ∀ (h : Gate 2) → (₃₊ n) ⊢ [ gate₂ h ]ʷ ↑ • Swap • Swap ↑ ≈ Swap • Swap ↑ • [ gate₂ h ]ʷ
swap₂ CS-gate = swap-CS
