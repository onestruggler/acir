{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D007 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain


-- CCZ013-T: 2 steps (scratchpad/four/lower.py)
lem-CCZ013-T : ⟪ (CCZ013 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ013-T = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸
       at 1 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸ done

