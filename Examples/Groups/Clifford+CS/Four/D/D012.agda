{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D012 where

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


-- CS13 passes T: 25 steps (scratchpad/four/lower.py)
lem-CS13-passes-T : ⟪ (CS13 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS13 ∷ []) ⟫ʷ
lem-CS13-passes-T = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS13 ∷ Toff012 ∷ []) (K0 ∷ CS02 ∷ CX12 ∷ CS13 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (Toff) (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ CS13 ∷ []) (sym (low₁-comm (K) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS01 ∷ CS23 ∷ []) (sym (low-comm (CS) (CS))) ▸
       at 3 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (K0 ∷ CS02 ∷ CX12 ∷ CS13 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ K0⁻ ∷ [])
  b1 = at 4 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 5 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸ done

  b2 : Chain (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ K0⁻ ∷ []) (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ CS13 ∷ [])
  b2 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CS01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • CS) (CS • (CS ↑)) tt tt Eq.refl) ▸
       at 5 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (K0⁻ ∷ CS13 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑ • CS • Swap ↑)))) ▸ done

  b3 : Chain (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ CS13 ∷ []) (Toff012 ∷ CS13 ∷ [])
  b3 = at 0 7 (Toff012 ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) (Toff) tt tt Eq.refl) ▸ done

