{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D015 where

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


-- comm CCZ123 CSd02: 21 steps (scratchpad/four/lower.py)
lem-comm-CCZ123-CSd02 : ⟪ (CCZ123 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CSd02 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ123 ∷ CS02⁻ ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS02⁻ ∷ CS23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 2 (CS12⁻ ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (CS • CS • CS)) ((CS • CS • CS) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS02⁻ ∷ CS23 ∷ []) (CS12 ∷ Sw12 ∷ CX32 ∷ CS01⁻ ∷ Sw12 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ [])
  b1 = at 4 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS01⁻ ∷ CX32 ∷ []) (sym (low-comm ((CS • CS • CS)) (CX₁₀))) ▸
       at 5 2 (Sw12 ∷ CX31 ∷ []) (win 0 3 complete₃ ((CX₁₀ ↑) • Swap) (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS02⁻ ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ Sw12 ∷ CX32 ∷ CS01⁻ ∷ Sw12 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CS02⁻ ∷ CCZ123 ∷ [])
  b2 = at 2 2 (CS01⁻ ∷ CX32 ∷ []) (sym (low-comm ((CS • CS • CS)) (CX₁₀))) ▸
       at 3 2 (Sw12 ∷ CX31 ∷ []) (win 0 3 complete₃ ((CX₁₀ ↑) • Swap) (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸ done

