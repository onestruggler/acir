{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D021 where

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
open import Examples.Groups.Clifford+CS.Four.D.D020 using (lem-CS12-passes-T)

-- CS12 passes PP3: 20 steps (scratchpad/four/lower.py)
lem-CS12-passes-PP3 : ⟪ (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-CS12-passes-PP3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (Toff012 ∷ CS12 ∷ []) (lem-CS12-passes-T) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS01 ∷ CS23 ∷ []) (sym (low-comm (CS) (CS))) ▸
       at 4 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Toff012 ∷ CS12 ∷ []) (lem-CS12-passes-T) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 5 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ [])
  b2 = at 6 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

