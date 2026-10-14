{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D054 where

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
open import Examples.Groups.Clifford+CS.Four.D.D053 using (lem-C3-Ai)
open import Examples.Groups.Clifford+CS.Four.D.D003 using (lem-T-CZ03-T)
open import Examples.Groups.Clifford+CS.Four.D.D024 using (lem-comm-CCZ123-CS03)

-- PPi2=E: 22 steps (scratchpad/four/lower.py)
lem-PPi2≡E : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-PPi2≡E = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ [])
  b0 = at 4 4 (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ []) (lem-C3-Ai) ▸
       at 3 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CZ02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ []) (CCZ123 ∷ CS03 ∷ CZ03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 3 (CCZ123 ∷ CZ03 ∷ []) (lem-T-CZ03-T) ▸
       at 0 2 (CCZ123 ∷ CS03 ∷ []) (sym lem-comm-CCZ123-CS03) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ123 ∷ CS03 ∷ CZ03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ []) (CCZ123 ∷ [])
  b2 = at 2 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 3 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

