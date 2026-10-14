{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D059 where

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


-- comm CZ01 CCZ123: 15 steps (scratchpad/four/lower.py)
lem-comm-CZ01-CCZ123 : ⟪ (CZ01 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CZ01 ∷ []) ⟫ʷ
lem-comm-CZ01-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ01 ∷ CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CZ01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (CS12 ∷ CZ01 ∷ []) (win 3 0 complete₃ (CZ • (CS ↑)) ((CS ↑) • CZ) tt tt Eq.refl) ▸
       at 1 2 (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀)) ▸
       at 2 2 (CS12⁻ ∷ CZ01 ∷ []) (win 3 0 complete₃ (CZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CZ) tt tt Eq.refl) ▸
       at 3 2 (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CZ01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ []) (CCZ123 ∷ CZ01 ∷ [])
  b1 = at 4 2 (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap)) ▸
       at 5 2 (CS12 ∷ CZ01 ∷ []) (win 3 0 complete₃ (CZ • (CS ↑)) ((CS ↑) • CZ) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) tt tt Eq.refl) ▸ done

