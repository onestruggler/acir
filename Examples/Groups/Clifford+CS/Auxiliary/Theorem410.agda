------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of P′ are complete: the analogue of Clément's Theorem 4.10
--
-- The Reidemeister–Schreier method turns items (a) (`ItemA`) and (b)
-- (`ItemB`) into reflection: two words over P′ whose two-level
-- spellings are equivalent by Bian and Selinger's relations are
-- equivalent by the rules of P′ (`reidemeister-schreier`).  Together
-- with soundness (`Sound`), the rules of P′ and the two-level relations
-- identify exactly the same words.  And the two-level relations are
-- complete for the matrix semantics (Clifford+CS-TwoLevel's
-- `relations-complete`, proved there from the exact synthesis
-- algorithm), so the rules of P′ are complete for it too (`complete`):
-- two words over P′ with the same matrix are equivalent.  Clément has
-- to import the corresponding Theorem 4.4; here it is a theorem, so
-- this is unconditional.
--
-- Stated for N ≥ 16 indices, which every width from four qubits on
-- has.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.Theorem410
  (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (Word ; _ʷ)

import Presentation.Base as PB

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (⟦_⟧ᵐ)
open import Examples.Groups.Clifford+CS-TwoLevel.MainLemma {suc N′}
  using (relations-complete)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
open import Examples.Groups.Clifford+CS.Auxiliary.RS N′ big using (module Complete)
open import Examples.Groups.Clifford+CS.Auxiliary.ItemA N′ big using (item-a)
open import Examples.Groups.Clifford+CS.Auxiliary.ItemB N′ big using (item-b)
import Examples.Groups.Clifford+CS.Auxiliary.Sound as Sound

private
  N : ℕ
  N = suc N′

  _≈ᴾ_ : Word (GenP N) → Word (GenP N) → Set
  _≈ᴾ_ = PB._≈_ (N R,_===_)

  _≈ᵀ_ : Word (TL.Gen N) → Word (TL.Gen N) → Set
  _≈ᵀ_ = PB._≈_ (TL._===_ {N})

------------------------------------------------------------------------
-- The rules of P′ and the two-level relations agree

-- Reflection, by Reidemeister–Schreier.
reflects : ∀ (w v : Word (GenP N)) → (asG ʷ) w ≈ᵀ (asG ʷ) v → w ≈ᴾ v
reflects = Complete.reidemeister-schreier item-a item-b

-- Preservation, by soundness.
preserves : ∀ {w v : Word (GenP N)} → w ≈ᴾ v → (asG ʷ) w ≈ᵀ (asG ʷ) v
preserves = Sound.sound N

------------------------------------------------------------------------
-- Completeness for the matrix semantics

complete : ∀ {w v : Word (GenP N)} →
           ⟦ (asG ʷ) w ⟧ᵐ ≡ ⟦ (asG ʷ) v ⟧ᵐ → w ≈ᴾ v
complete {w} {v} e = reflects w v (relations-complete e)
