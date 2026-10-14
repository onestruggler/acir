{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D064 where

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


-- SW12-PP: 17 steps (scratchpad/four/lower.py)
lem-SW12-PP : ⟪ (Sw12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-SW12-PP = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ []) (Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CS03⁻ ∷ Sw12 ∷ [])
  b0 = at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (Toff012 ∷ []) (win 3 0 complete₃ ((Swap ↑) • Toff • (Swap ↑)) (Toff) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 4 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CS03⁻ ∷ Sw12 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 3 (Toff012 ∷ []) (win 3 0 complete₃ ((Swap ↑) • Toff • (Swap ↑)) (Toff) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 6 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ Sw12 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b2 = at 4 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

