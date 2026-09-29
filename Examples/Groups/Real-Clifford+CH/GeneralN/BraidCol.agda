------------------------------------------------------------------------
-- Presentations of groups
--
-- The braid of two crossed rotations, as a statement (Clément, Appendix
-- E.5, rule (24))
--
-- `Braid m` says that two rotations placed on the targets t ≠ t′, whose
-- colourings agree off the two targets and whose types are read off
-- the other one's colour on their own target (as for two consecutive
-- Gray-code steps), satisfy the braid relation.  Like RotCol, this module
-- has no parameters, so that the proof at width 5 + k (BraidAnywhere)
-- and the rule that uses it (Lemma88.Rule24) spell the statement alike.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.BraidCol where

open import Data.Bool using (Bool ; true ; not)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)

Braid : ℕ → Set
Braid m =
  ∀ α β (u u′ : Word (S.Gen (₃₊ m))) (t t′ : Fin (₃₊ m)) → t′ ≢ t →
  perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F → (s s′ : Bits (₃₊ m)) →
  lookupℕ (toℕ t) s ≡ true → lookupℕ (toℕ t′) s′ ≡ true →
  (∀ (j : Fin (₃₊ m)) → j ≢ t → j ≢ t′ → lookupℕ (toℕ j) s ≡ lookupℕ (toℕ j) s′) →
  not α ≡ lookupℕ (toℕ t) s′ → β ≡ lookupℕ (toℕ t′) s →
  (₃₊ m) ⊢ place u s (rot α) • place u′ s′ (rot β) • place u s (rot α) ≈
           place u′ s′ (rot β) • place u s (rot α) • place u′ s′ (rot β)
