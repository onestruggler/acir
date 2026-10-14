{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D045 where

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
open import Examples.Groups.Clifford+CS.Four.D.D043 using (lem-T1-CZ13-T1)
open import Examples.Groups.Clifford+CS.Four.D.D044 using (lem-comm-CCZ012-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D035 using (lem-comm-CCZ012-CZ13)

-- B=F: 5 steps (scratchpad/four/lower.py)
lem-B≡F : ⟪ (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-B≡F = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ [])
  b0 = at 1 3 (CCZ023 ∷ CZ13 ∷ []) (lem-T1-CZ13-T1) ▸
       at 0 2 (CCZ023 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CCZ023) ▸
       at 1 2 (CZ13 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CZ13) ▸
       at 2 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

