------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.7 on three qubits
--
-- Split off from Lemma87All because it needs completeness on two qubits
-- only: an induction on the width that proves completeness on three
-- from Lemma 8.7 on three cannot pass completeness on three to it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Three
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; s≤s)
open import Word.Base using (_•_)

open import Notations using (₂₊)

open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.Section8 using (Lemma-8-7)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon3 complete₂ using (canon3 ; merge3)
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87 as L87

-- The merges Lemma87 needs, up to width 2 + B.
Merges : ℕ → Set
Merges B = ∀ K → 1 ≤ K → K ≤ B → ∀ c → 1 ≤ c → c ≤ suc K →
           (₂₊ K) ⊢ (Xat c • Λ□ (suc K) • Xat c) • Λ□ (suc K) ≈ placeAt c (Λ□ K)

merges₁ : Merges 1
merges₁ (suc zero) _ _ = merge3
merges₁ zero       ()
merges₁ (suc (suc K)) _ (s≤s ())

lemma-8-7₃ : Lemma-8-7 0
lemma-8-7₃ = L87.lemma-8-7 canon3 merges₁ complete₂
