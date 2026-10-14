{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D057 where

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

-- PP-flip: 46 steps (scratchpad/four/lower.py)
lem-PP-flip : ⟪ (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-PP-flip = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (Toff012 ∷ X0 ∷ Sw23 ∷ CS02 ∷ X0 ∷ Sw23 ∷ X0 ∷ Toff012 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ [])
  b0 = at 4 0 (X0 ∷ X0 ∷ []) (win 3 0 complete₃ (ε) (X • X) tt tt Eq.refl) ▸
       at 3 0 (X0 ∷ X0 ∷ []) (win 3 0 complete₃ (ε) (X • X) tt tt Eq.refl) ▸
       at 2 0 (X0 ∷ X0 ∷ []) (win 3 0 complete₃ (ε) (X • X) tt tt Eq.refl) ▸
       at 0 3 (Toff012 ∷ []) (win 3 0 complete₃ (X • Toff • X) (Toff) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ X0 ∷ Sw23 ∷ CS02 ∷ X0 ∷ Sw23 ∷ X0 ∷ Toff012 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (Toff012 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 1 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 2 3 (S2 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • CS • Swap ↑) • X) ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 3 (Toff012 ∷ []) (win 3 0 complete₃ (X • Toff • X) (Toff) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ Sw23 ∷ Sw23 ∷ []) (Toff012 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ S3⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 6 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 5 3 (CS02 ∷ S2⁻ ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑ ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (S3⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (Toff012 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ S3⁻ ∷ Sw23 ∷ Sw23 ∷ []) (Toff012 ∷ CS03⁻ ∷ Sw23 ∷ S2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ S3⁻ ∷ [])
  b3 = at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS02⁻ ∷ S2 ∷ []) (win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Toff012 ∷ CS03⁻ ∷ Sw23 ∷ S2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ S3⁻ ∷ []) (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ S2 ∷ Sw23 ∷ S3⁻ ∷ [])
  b4 = at 2 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ S3 ∷ []) (sym (low₃-comm (Toff) (S))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS02 ∷ S2 ∷ []) (win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S ↑ ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ S2 ∷ Sw23 ∷ S3⁻ ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b5 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((S ↑ ↑) • ((S • S • S) ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-C3-Ai) ▸ done

