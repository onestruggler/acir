{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D035 where

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


-- comm CCZ012 CZ13: 51 steps (scratchpad/four/lower.py)
lem-comm-CCZ012-CZ13 : ⟪ (CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CZ13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ012 ∷ CZ13 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CZ13 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ CX20 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CX20 ∷ CS12 ∷ [])
  b1 = at 7 2 (CZ23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CZ23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CZ)) ▸
       at 5 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ CX20 ∷ CS01⁻ ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CX20 ∷ CS12 ∷ []) (CS01 ∷ CX20 ∷ CZ13 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ CX20 ∷ CS12 ∷ [])
  b2 = at 3 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 3 2 (CZ12 ∷ CS01⁻ ∷ []) (win 3 0 complete₃ ((CS • CS • CS) • (CZ ↑)) ((CZ ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS01 ∷ CX20 ∷ CZ13 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ CX20 ∷ CS12 ∷ []) (CS01 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b3 = at 3 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CS01 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b4 = at 5 2 (CZ23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CZ23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CZ)) ▸
       at 3 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CZ13 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b5 = at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 1 2 (CZ12 ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • (CZ ↑)) ((CZ ↑) • CS) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CZ13 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CZ13 ∷ CCZ012 ∷ [])
  b6 = at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸ done

