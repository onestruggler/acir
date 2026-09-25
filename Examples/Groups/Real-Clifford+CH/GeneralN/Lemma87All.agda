------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.7 at every width
--
-- Lemma87 takes the canonical box facts at the width and the merge (309)
-- at every width up to it.  On three qubits both come from completeness
-- on two (Canon3), on four from Lemma D.5 (Canon4), and on 5 + k from
-- completeness at every width up to 4 + k, the paper's own induction
-- (CanonN; BoxMergeAt for the merges on five qubits and more).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.Section8 using (Lemma-8-7)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon3 complete₂ using (canon3 ; merge3)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4 ; merge4)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMergeAt complete₂ complete₃ using (merge-at′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87 as L87

-- The merges Lemma87 needs, up to width 2 + B.
Merges : ℕ → Set
Merges B = ∀ K → 1 ≤ K → K ≤ B → ∀ c → 1 ≤ c → c ≤ suc K →
           (₂₊ K) ⊢ (Xat c • Λ□ (suc K) • Xat c) • Λ□ (suc K) ≈ placeAt c (Λ□ K)

merges₁ : Merges 1
merges₁ (suc zero) _ _ = merge3
merges₁ zero       ()
merges₁ (suc (suc K)) _ (s≤s ())

merges₂ : Merges 2
merges₂ (suc zero)       _ _ = merge3
merges₂ (suc (suc zero)) _ _ = merge4
merges₂ zero             ()
merges₂ (suc (suc (suc K))) _ (s≤s (s≤s ()))

-- From completeness at every width up to 4 + k.
mergesₙ : ∀ k → Completes (₁₊ k) → Merges (₃₊ k)
mergesₙ k cs (suc zero)          _ _    = merge3
mergesₙ k cs (suc (suc zero))    _ _    = merge4
mergesₙ k cs zero                ()
mergesₙ k cs (suc (suc (suc j))) _ (s≤s (s≤s (s≤s j≤k))) (suc c) _ (s≤s c≤) =
  merge-at′ j (cs (s≤s j≤k)) (eqSymAt (₁₊ j) (λ i≤ → cs (≤-trans i≤ (s≤s j≤k)))) c (s≤s c≤)
mergesₙ k cs (suc (suc (suc j))) _ _ zero () _

lemma-8-7₃ : Lemma-8-7 0
lemma-8-7₃ = L87.lemma-8-7 canon3 merges₁ complete₂

lemma-8-7₄ : Lemma-8-7 1
lemma-8-7₄ = L87.lemma-8-7 canon4 merges₂ complete₂

lemma-8-7ₙ : ∀ k → Completes (₁₊ k) → Lemma-8-7 (₂₊ k)
lemma-8-7ₙ k cs = L87.lemma-8-7 (canonN k cs) (mergesₙ k cs) complete₂
