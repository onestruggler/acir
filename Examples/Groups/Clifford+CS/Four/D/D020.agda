{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D020 where

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


-- CS12 passes T: 1 steps (scratchpad/four/lower.py)
lem-CS12-passes-T : ⟪ (CS12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12 ∷ []) ⟫ʷ
lem-CS12-passes-T = run b0
  where
  b0 : Chain (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ [])
  b0 = at 0 2 (Toff012 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) tt tt Eq.refl) ▸ done

